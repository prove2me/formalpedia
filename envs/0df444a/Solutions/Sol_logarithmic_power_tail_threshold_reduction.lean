-- Prove2me | solution 1 for logarithmic_power_tail_threshold_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T02:43:51.302069+00:00
-- url     : https://prove2.me/submissions/edbd6367-3b16-41b6-bdde-7c98a5d9b301

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import Definitions.Def_weightedLogMass

open scoped BigOperators
open scoped Topology
open Filter
open Classical

noncomputable section

theorem tendsto_const_div_log_nat_atTop (C : ℝ) :
    Tendsto (fun n : ℕ => C / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hlog.const_div_atTop C

theorem log_power_bound_gives_fixed_cutoff_tightness
    (A : ℕ → ℕ → ℝ) (C c : ℝ) (_hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ M x, 2 ≤ M → 2 ≤ x →
      A M x ≤ C / Real.rpow (Real.log (M : ℝ)) c) :
    ∀ ε > 0, ∃ M, 2 ≤ M ∧ ∀ x, 2 ≤ x → A M x < ε := by
  intro ε hε
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun M : ℕ => Real.rpow (Real.log (M : ℝ)) c) atTop atTop := by
    exact (tendsto_rpow_atTop hc).comp hlog
  have hrate : Tendsto (fun M : ℕ => C / Real.rpow (Real.log (M : ℝ)) c)
      atTop (𝓝 0) := by
    exact hpow.const_div_atTop C
  have hev : ∀ᶠ M : ℕ in atTop, C / Real.rpow (Real.log (M : ℝ)) c < ε :=
    hrate.eventually (eventually_lt_nhds hε)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hev
  let M := max 2 M₀
  refine ⟨M, le_max_left 2 M₀, ?_⟩
  intro x hx
  exact lt_of_le_of_lt (hbound M x (le_max_left 2 M₀) hx) (hM₀ M (le_max_right 2 M₀))

theorem logarithmic_threshold_reduction
    (D : ℕ → Prop) (w P f : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k)
    (hfixed : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ cutoff : ℕ, 2 ≤ cutoff →
        weightedLogMass D (fun k => M < P k) w cutoff < ε)
    (hf : Tendsto f atTop atTop) :
    Tendsto (fun cutoff : ℕ =>
      weightedLogMass D (fun k => P k ≥ f k) w cutoff) atTop (𝓝 0) := by
  classical
  have hmass_nonneg : ∀ᶠ cutoff : ℕ in atTop,
      0 ≤ weightedLogMass D (fun k => P k ≥ f k) w cutoff := by
    filter_upwards [eventually_ge_atTop 2] with cutoff hcutoff
    unfold weightedLogMass
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      split_ifs with h
      · exact hw k
      · exact le_rfl
    · exact (Real.log_pos (by exact_mod_cast (show 1 < cutoff by omega))).le
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hmass_nonneg] with cutoff hnonneg
    exact ha.trans_le hnonneg
  · intro ε hε
    obtain ⟨M, hM⟩ := hfixed (ε / 2) (by linarith)
    rcases eventually_atTop.1 (hf.eventually_gt_atTop M) with ⟨N, hN⟩
    let K : ℝ := ∑ k ∈ Finset.range N, if D k then w k else 0
    have hK : ∀ᶠ cutoff : ℕ in atTop, K / Real.log (cutoff : ℝ) < ε / 2 := by
      have hlim : Tendsto (fun cutoff : ℕ => K / Real.log (cutoff : ℝ)) atTop (𝓝 0) := by
        dsimp [K]
        exact tendsto_const_div_log_nat_atTop _
      exact hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop N, hK]
      with cutoff hcutoff hNcutoff hKcutoff
    have hprefix :
        (∑ k ∈ Finset.range (cutoff + 1),
          if D k ∧ k < N then w k else 0) = K := by
      have hsubset : Finset.range N ⊆ Finset.range (cutoff + 1) := by
        intro k hk
        exact Finset.mem_range.2 (by
          have hkN : k < N := Finset.mem_range.1 hk
          omega)
      calc
        (∑ k ∈ Finset.range (cutoff + 1),
            if D k ∧ k < N then w k else 0) =
            ∑ k ∈ Finset.range N, if D k ∧ k < N then w k else 0 := by
              symm
              apply Finset.sum_subset hsubset
              intro k hk hnot
              have hkN : ¬k < N := by
                intro hkN
                exact hnot (Finset.mem_range.2 hkN)
              simp [hkN]
        _ = K := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkN : k < N := Finset.mem_range.1 hk
          simp [hkN]
    have hsum :
        (∑ k ∈ Finset.range (cutoff + 1),
          if D k ∧ P k ≥ f k then w k else 0) ≤
          (∑ k ∈ Finset.range (cutoff + 1),
            if D k ∧ M < P k then w k else 0) + K := by
      calc
        (∑ k ∈ Finset.range (cutoff + 1),
            if D k ∧ P k ≥ f k then w k else 0) ≤
            ∑ k ∈ Finset.range (cutoff + 1),
              ((if D k ∧ M < P k then w k else 0) +
                (if D k ∧ k < N then w k else 0)) := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hD : D k
          · by_cases hkN : k < N
            · by_cases hvar : P k ≥ f k
              · by_cases htail : M < P k
                · simp [hD, hkN, hvar, htail]
                  linarith [hw k]
                · simp [hD, hkN, hvar, htail]
              · by_cases htail : M < P k
                · simp [hD, hkN, hvar, htail]
                  exact hw k
                · simp [hD, hkN, hvar, htail]
                  exact hw k
            · have hkN' : N ≤ k := Nat.le_of_not_gt hkN
              have hMf : M < f k := hN k hkN'
              by_cases hvar : P k ≥ f k
              · have htail : M < P k := lt_of_lt_of_le hMf hvar
                simp [hD, hkN, hvar, htail]
              · by_cases htail : M < P k
                · simp [hD, hkN, hvar, htail, hw k]
                · simp [hD, hkN, hvar, htail]
          · simp [hD]
        _ = (∑ k ∈ Finset.range (cutoff + 1),
              if D k ∧ M < P k then w k else 0) + K := by
          rw [Finset.sum_add_distrib, hprefix]
    have hlogpos : 0 < Real.log (cutoff : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < cutoff by omega)
    have hmass_le :
        weightedLogMass D (fun k => P k ≥ f k) w cutoff ≤
          weightedLogMass D (fun k => M < P k) w cutoff + K /
            Real.log (cutoff : ℝ) := by
      unfold weightedLogMass
      calc
        (∑ k ∈ Finset.range (cutoff + 1),
              if D k ∧ P k ≥ f k then w k else 0) /
            Real.log (cutoff : ℝ) ≤
            ((∑ k ∈ Finset.range (cutoff + 1),
                if D k ∧ M < P k then w k else 0) + K) /
              Real.log (cutoff : ℝ) :=
          div_le_div_of_nonneg_right hsum hlogpos.le
        _ = weightedLogMass D (fun k => M < P k) w cutoff +
            K / Real.log (cutoff : ℝ) := by
          rw [weightedLogMass]
          ring
    have htail := hM cutoff hcutoff
    linarith

theorem solution
    (D : ℕ → Prop) (w P f : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ M x : ℕ, 2 ≤ M → 2 ≤ x →
      weightedLogMass D (fun k => (M : ℝ) < P k) w x ≤
        C / Real.rpow (Real.log (M : ℝ)) c)
    (hf : Tendsto f atTop atTop) :
    Tendsto (fun cutoff : ℕ =>
      weightedLogMass D (fun k => P k ≥ f k) w cutoff) atTop (𝓝 0) := by
  apply logarithmic_threshold_reduction D w P f hw
  intro ε hε
  obtain ⟨M, _hM, hMx⟩ :=
    log_power_bound_gives_fixed_cutoff_tightness
      (fun M x => weightedLogMass D (fun k => (M : ℝ) < P k) w x)
      C c hC hc hbound ε hε
  refine ⟨(M : ℝ), ?_⟩
  intro cutoff hcutoff
  simpa using hMx cutoff hcutoff
  exact hf
