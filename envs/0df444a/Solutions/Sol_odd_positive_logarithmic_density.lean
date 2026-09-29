-- Prove2me | solution 1 for odd_positive_logarithmic_density
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T03:45:41.288584+00:00
-- url     : https://prove2.me/submissions/534ef1d7-6af7-4708-b310-464c7bd5ccfa

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import Definitions.Def_weightedLogMass
import Definitions.Def_weightedLogMassReal

open scoped BigOperators
open scoped Topology
open Filter
open Classical

noncomputable section

/-!
# Standalone platform proof of the positive odd real normalization

This file deliberately imports only Mathlib and the two weighted-mass
definitions.  The harmonic finite identity, its natural-cutoff limit, and the
real floor-cutoff lift are all proved locally for platform verification.
-/

theorem platform_odd_harmonic_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      if 0 < k ∧ Odd k then 1 / (k : ℝ) else 0) =
      (harmonic n : ℝ) - (1 / 2 : ℝ) * (harmonic (n / 2) : ℝ) := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (n + 1 + 1),
            if 0 < k ∧ Odd k then 1 / ((k : ℕ) : ℝ) else 0) =
            (∑ k ∈ Finset.range (n + 1),
              if 0 < k ∧ Odd k then 1 / (k : ℝ) else 0) +
              (if 0 < n + 1 ∧ Odd (n + 1) then 1 / ((n + 1 : ℕ) : ℝ) else 0) := by
                rw [Finset.sum_range_succ]
        _ = (harmonic n : ℝ) - (1 / 2 : ℝ) * (harmonic (n / 2) : ℝ) +
              (if 0 < n + 1 ∧ Odd (n + 1) then 1 / ((n + 1 : ℕ) : ℝ) else 0) := by
                rw [ih]
        _ = (harmonic (n + 1) : ℝ) -
              (1 / 2 : ℝ) * (harmonic ((n + 1) / 2) : ℝ) := by
                rcases Nat.even_or_odd n with hn | hn
                · obtain ⟨k, rfl⟩ := hn
                  have hdiv₁ : (k + k) / 2 = k := by omega
                  have hdiv₂ : (k + k + 1) / 2 = k := by omega
                  have hodd : Odd (k + k + 1) := by
                    rw [Nat.odd_iff]
                    omega
                  simp [hdiv₁, hdiv₂, hodd, harmonic_succ]
                  ring
                · obtain ⟨k, rfl⟩ := hn
                  have hdiv₁ : (2 * k + 1) / 2 = k := by omega
                  have hdiv₂ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
                  have hnotodd : ¬ Odd (2 * k + 1 + 1) := by
                    rw [Nat.odd_iff]
                    omega
                  simp [hdiv₁, hdiv₂, hnotodd, harmonic_succ]
                  field_simp
                  ring

theorem platform_tendsto_harmonic_div_log :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror :
      Tendsto
        (fun n : ℕ =>
          ((harmonic n : ℝ) - Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (𝓝 0) := by
    exact Real.tendsto_harmonic_sub_log.div_atTop hlog
  have hself :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    refine (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    simp [hpos.ne']
  simpa [sub_div] using herror.add hself

theorem platform_tendsto_log_nat_div_two_div_log_nat :
    Tendsto
      (fun n : ℕ => Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconstdiv :
      Tendsto (fun n : ℕ => Real.log (4 : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 0) := hlog.const_div_atTop (Real.log 4)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      0 ≤ 1 - Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) ∧
        1 - Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) ≤
          Real.log (4 : ℝ) / Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : 0 < n := by omega
    have hmpos : 0 < n / 2 := by omega
    have hlogn : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hlogm_le : Real.log ((n / 2 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hmpos)
        (by exact_mod_cast (Nat.div_le_self n 2))
    have hmul : n ≤ 4 * (n / 2) := by omega
    have hlog_bound : Real.log (n : ℝ) ≤
        Real.log (4 : ℝ) + Real.log ((n / 2 : ℕ) : ℝ) := by
      calc
        Real.log (n : ℝ) ≤ Real.log ((4 : ℝ) * (n / 2 : ℕ)) := by
          exact Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hmul)
        _ = Real.log (4 : ℝ) + Real.log ((n / 2 : ℕ) : ℝ) := by
          rw [Real.log_mul]
          · norm_num
          · exact_mod_cast hmpos.ne'
    have hratio_lower :
        1 - Real.log (4 : ℝ) / Real.log (n : ℝ) ≤
          Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) := by
      calc
        1 - Real.log (4 : ℝ) / Real.log (n : ℝ) =
            (Real.log (n : ℝ) - Real.log (4 : ℝ)) / Real.log (n : ℝ) := by
              field_simp [hlogn.ne']
        _ ≤ Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) := by
          exact div_le_div_of_nonneg_right (by linarith) hlogn.le
    have hratio_upper :
        Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hlogn]
      linarith
    constructor <;> linarith
  have hzero := squeeze_zero'
    (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)
    hconstdiv
  have hone := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
  simpa only [sub_sub_cancel, sub_zero] using hone

theorem platform_tendsto_harmonic_nat_div_two_div_log :
    Tendsto
      (fun n : ℕ => (harmonic (n / 2) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro m
    filter_upwards [eventually_ge_atTop (2 * m)] with n hn
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hharmonic :
      Tendsto
        (fun n : ℕ =>
          (harmonic (n / 2) : ℝ) / Real.log ((n / 2 : ℕ) : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    simpa [Function.comp_def] using platform_tendsto_harmonic_div_log.comp hdiv
  have hprod := hharmonic.mul platform_tendsto_log_nat_div_two_div_log_nat
  have hprod' := hprod.congr' (show
      (fun n : ℕ =>
        (harmonic (n / 2) : ℝ) / Real.log ((n / 2 : ℕ) : ℝ) *
          (Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ))) =ᶠ[atTop]
        (fun n : ℕ => (harmonic (n / 2) : ℝ) / Real.log (n : ℝ)) by
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hlogm : 0 < Real.log ((n / 2 : ℕ) : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n / 2 by omega)
    exact div_mul_div_cancel₀ hlogm.ne')
  simpa using hprod'

theorem platform_weightedLogMass_odd_positive_true_tendsto_half :
    Tendsto
      (fun n : ℕ =>
        weightedLogMass
          (fun k => 0 < k ∧ Odd k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) n)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmass : ∀ n : ℕ,
      weightedLogMass
          (fun k => 0 < k ∧ Odd k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) n =
        (harmonic n : ℝ) / Real.log (n : ℝ) -
          (1 / 2 : ℝ) * ((harmonic (n / 2) : ℝ) / Real.log (n : ℝ)) := by
    intro n
    unfold weightedLogMass
    simp only [and_true]
    rw [platform_odd_harmonic_sum_eq]
    ring
  have hlim := platform_tendsto_harmonic_div_log.sub
    ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).mul
      platform_tendsto_harmonic_nat_div_two_div_log)
  have hlim' : Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) / Real.log (n : ℝ) -
          (1 / 2 : ℝ) * ((harmonic (n / 2) : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    convert hlim using 1
    norm_num
  apply hlim'.congr'
  filter_upwards [] with n
  exact (hmass n).symm

theorem platform_tendsto_log_nat_floor_div_log_real :
    Tendsto
      (fun x : ℝ => Real.log (⌊x⌋₊ : ℝ) / Real.log x)
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hconstdiv :
      Tendsto (fun x : ℝ => Real.log (2 : ℝ) / Real.log x)
        atTop (𝓝 0) := hlog.const_div_atTop (Real.log 2)
  have hbounds : ∀ᶠ x : ℝ in atTop,
      0 ≤ 1 - Real.log (⌊x⌋₊ : ℝ) / Real.log x ∧
        1 - Real.log (⌊x⌋₊ : ℝ) / Real.log x ≤
          Real.log (2 : ℝ) / Real.log x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx_nonneg : (0 : ℝ) ≤ x := by linarith
    have hfloor_two : 2 ≤ ⌊x⌋₊ := by
      exact (Nat.le_floor_iff' (by omega : 2 ≠ 0)).2 (by exact_mod_cast hx)
    have hfloor_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogfloor : 0 < Real.log (⌊x⌋₊ : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have hlogfloor_le : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log hfloor_pos hfloor_le
    have hxfloor : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have hone : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by linarith
      linarith
    have hlog_bound : Real.log x ≤
        Real.log (2 : ℝ) + Real.log (⌊x⌋₊ : ℝ) := by
      calc
        Real.log x ≤ Real.log ((2 : ℝ) * (⌊x⌋₊ : ℝ)) :=
          Real.log_le_log (by linarith) hxfloor
        _ = Real.log (2 : ℝ) + Real.log (⌊x⌋₊ : ℝ) := by
          rw [Real.log_mul]
          · norm_num
          · exact hfloor_pos.ne'
    have hratio_lower : 1 - Real.log (2 : ℝ) / Real.log x ≤
        Real.log (⌊x⌋₊ : ℝ) / Real.log x := by
      calc
        1 - Real.log (2 : ℝ) / Real.log x =
            (Real.log x - Real.log (2 : ℝ)) / Real.log x := by
              field_simp [hlogx.ne']
        _ ≤ Real.log (⌊x⌋₊ : ℝ) / Real.log x :=
          div_le_div_of_nonneg_right (by linarith) hlogx.le
    have hratio_upper : Real.log (⌊x⌋₊ : ℝ) / Real.log x ≤ 1 := by
      rw [div_le_iff₀ hlogx]
      linarith
    constructor <;> linarith
  have hzero := squeeze_zero'
    (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)
    hconstdiv
  have hone := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
  simpa only [sub_sub_cancel, sub_zero] using hone

theorem platform_weightedLogMassReal_eq_nat_floor_mul_log_ratio
    (D E : ℕ → Prop) (w : ℕ → ℝ) :
    ∀ᶠ x : ℝ in atTop,
      weightedLogMassReal D E w x =
        weightedLogMass D E w ⌊x⌋₊ *
          (Real.log (⌊x⌋₊ : ℝ) / Real.log x) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx_nonneg : (0 : ℝ) ≤ x := by linarith
  have hfloor_two : 2 ≤ ⌊x⌋₊ := by
    exact (Nat.le_floor_iff' (by omega : 2 ≠ 0)).2 (by exact_mod_cast hx)
  have hlogfloor : Real.log (⌊x⌋₊ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))).ne'
  have hlogx : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  unfold weightedLogMassReal weightedLogMass
  field_simp [hlogfloor, hlogx]

theorem platform_weightedLogMass_nat_limit_to_real_of_limit
    (D E : ℕ → Prop) (w : ℕ → ℝ) (L : ℝ)
    (hlim : Tendsto (fun n : ℕ => weightedLogMass D E w n) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => weightedLogMassReal D E w x) atTop (𝓝 L) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hmass : Tendsto
      (fun x : ℝ => weightedLogMass D E w ⌊x⌋₊) atTop (𝓝 L) :=
    hlim.comp hfloor
  have hprod : Tendsto
      (fun x : ℝ => weightedLogMass D E w ⌊x⌋₊ *
        (Real.log (⌊x⌋₊ : ℝ) / Real.log x))
      atTop (𝓝 (L * 1)) :=
    hmass.mul platform_tendsto_log_nat_floor_div_log_real
  have hprod' := hprod.congr'
    ((platform_weightedLogMassReal_eq_nat_floor_mul_log_ratio D E w).mono
      fun _ h => h.symm)
  simpa using hprod'

theorem solution :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun k => 0 < k ∧ Odd k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  exact platform_weightedLogMass_nat_limit_to_real_of_limit
    (fun k => 0 < k ∧ Odd k)
    (fun _ => True)
    (fun k => 1 / (k : ℝ))
    (1 / 2 : ℝ)
    platform_weightedLogMass_odd_positive_true_tendsto_half
