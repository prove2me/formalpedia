-- Prove2me | solution 1 for syracuse_offset_law_approximation
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T08:17:37.822003+00:00
-- url     : https://prove2.me/submissions/926f867e-e36b-4c87-957c-36a88e9262df

/- Standalone no-Solutions packaging of the Syracuse offset law.
   The accepted joint valuation theorem is imported as a platform mirror.
   All other adapters used by the finite offset pushforward are inlined here. -/

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_valuation_joint_geometric

set_option autoImplicit false

open MeasureTheory Set Nat ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

noncomputable section

namespace CollatzOffsetPackage



set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

/-- The singleton fibers of a countable-valued random variable have total mass one. -/
theorem countable_law_atoms_tsum
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    (∑' a : α, μ (X ⁻¹' ({a} : Set α))) = 1 := by
  have h := tsum_measure_preimage_singleton (μ := μ)
    (s := Set.univ) (Set.to_countable _) (f := X)
    (fun a _ => hX (MeasurableSet.singleton a))
  calc
    (∑' a : α, μ (X ⁻¹' ({a} : Set α))) =
        ∑' a : (Set.univ : Set α), μ (X ⁻¹' ({a.val} : Set α)) :=
      (tsum_univ (fun a : α => μ (X ⁻¹' ({a} : Set α)))).symm
    _ = 1 := by simpa only [Set.preimage_univ, measure_univ] using h

/-- Countable atom masses are summable as real numbers; no finite support is assumed. -/
theorem countable_law_atoms_summable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    Summable (fun a : α => (μ (X ⁻¹' ({a} : Set α))).toReal) := by
  apply ENNReal.summable_toReal
  rw [countable_law_atoms_tsum μ X hX]
  exact ENNReal.one_ne_top

/-- The real atom masses of a countable-valued probability law sum to one. -/
theorem countable_law_atoms_real_tsum
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    (∑' a : α, (μ (X ⁻¹' ({a} : Set α))).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => measure_ne_top μ _),
    countable_law_atoms_tsum μ X hX, ENNReal.toReal_one]

/-- A countable event has real mass equal to the sum of its atom masses. -/
theorem countable_law_event_real_tsum
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (E : Set α) :
    (∑' a : E, (μ (X ⁻¹' ({a.val} : Set α))).toReal) =
      (μ (X ⁻¹' E)).toReal := by
  rw [← ENNReal.tsum_toReal_eq (fun a => measure_ne_top μ _)]
  exact congrArg ENNReal.toReal
    (tsum_measure_preimage_singleton (μ := μ) (Set.to_countable E)
      (fun a _ => hX (MeasurableSet.singleton a)))


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open scoped BigOperators

set_option autoImplicit false

/-!
# Countable-source L1 contraction under a finite-valued map

Grouping two nonnegative summable laws over the fibers of a map into a finite
target cannot increase their L1 discrepancy.  The result is stated without a
normalization hypothesis so it can be reused for probability laws and model
weights alike.
-/

open scoped Classical in
theorem countable_l1_pushforward_contraction
    {α β : Type*} [Countable α] [Fintype β]
    (f : α → β) (p g : α → ℝ)
    (hp : Summable p) (hg : Summable g)
    (_hp_nonneg : ∀ a, 0 ≤ p a) (_hg_nonneg : ∀ a, 0 ≤ g a) :
    (∑ b : β,
        |(∑' a : {a // f a = b}, p a) -
          ∑' a : {a // f a = b}, g a|) ≤
      ∑' a : α, |p a - g a| := by
  classical
  have hdiff : Summable (fun a : α => p a - g a) := hp.sub hg
  have habs : Summable (fun a : α => |p a - g a|) := hdiff.abs
  have hfiber_diff (b : β) :
      Summable (fun a : {a // f a = b} => p a - g a) := by
    exact hdiff.subtype _
  have hfiber_p (b : β) :
      Summable (fun a : {a // f a = b} => p a) := by
    exact hp.subtype _
  have hfiber_g (b : β) :
      Summable (fun a : {a // f a = b} => g a) := by
    exact hg.subtype _
  have hfiber_eq (b : β) :
      (∑' a : {a // f a = b}, p a) -
          ∑' a : {a // f a = b}, g a =
        ∑' a : {a // f a = b}, (p a - g a) := by
    symm
    exact (hfiber_p b).tsum_sub (hfiber_g b)
  have hpoint (b : β) :
      |(∑' a : {a // f a = b}, p a) -
          ∑' a : {a // f a = b}, g a| ≤
        ∑' a : {a // f a = b}, |p a - g a| := by
    rw [hfiber_eq b]
    have hnorm : Summable (fun a : {a // f a = b} => ‖p a - g a‖) := by
      simpa only [Real.norm_eq_abs] using (hfiber_diff b).abs
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  have hfiber_total :
      (∑ b : β, ∑' a : {a // f a = b}, |p a - g a|) =
        ∑' a : α, |p a - g a| := by
    let e : (b : β) × {a // f a = b} ≃ α := Equiv.sigmaFiberEquiv f
    have hSigma : HasSum
        (fun x : (b : β) × {a // f a = b} => |p x.2 - g x.2|)
        (∑' a : α, |p a - g a|) := by
      simpa [e, Function.comp_def] using
        (e.hasSum_iff (f := fun a : α => |p a - g a|)).mpr habs.hasSum
    have hFiber (b : β) : HasSum
        (fun a : {a // f a = b} => |p a - g a|)
        (∑' a : {a // f a = b}, |p a - g a|) := by
      exact (habs.subtype (fun a : α => f a = b)).hasSum
    have hOuter := hSigma.sigma (fun b => hFiber b)
    have hOuter' : HasSum
        (fun b : β => ∑' a : {a // f a = b}, |p a - g a|)
        (∑' a : α, |p a - g a|) := by
      simpa [e] using hOuter
    rw [← hOuter'.tsum_eq, tsum_fintype]
  calc
    (∑ b : β,
        |(∑' a : {a // f a = b}, p a) -
          ∑' a : {a // f a = b}, g a|) ≤
        ∑ b : β, ∑' a : {a // f a = b}, |p a - g a| := by
      exact Finset.sum_le_sum (fun b hb => hpoint b)
    _ = ∑' a : α, |p a - g a| := hfiber_total


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open MeasureTheory Set
open scoped BigOperators

set_option autoImplicit false

/-!
# Countable law pushforward L1 contraction

The atomwise L1 discrepancy of two probability laws on a countable space
contracts after applying an arbitrary map into a finite target.  The source
laws are represented by measurable random variables on possibly different
probability spaces; no measurability of the map is required because each
target fiber is used only as a set in the countable event-mass identity.
-/

open scoped Classical in
theorem countable_law_pushforward_l1
    {Ω Ξ α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [Fintype β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : Ω → α) (Y : Ξ → α)
    (hX : Measurable X) (hY : Measurable Y)
    (f : α → β) :
    (∑ b : β,
        |(μ {ω | f (X ω) = b}).toReal -
          (ν {ξ | f (Y ξ) = b}).toReal|) ≤
      ∑' a : α,
        |(μ {ω | X ω = a}).toReal -
          (ν {ξ | Y ξ = a}).toReal| := by
  let p : α → ℝ := fun a => (μ (X ⁻¹' ({a} : Set α))).toReal
  let g : α → ℝ := fun a => (ν (Y ⁻¹' ({a} : Set α))).toReal
  have hp : Summable p := by
    simpa [p] using countable_law_atoms_summable μ X hX
  have hg : Summable g := by
    simpa [g] using countable_law_atoms_summable ν Y hY
  have hp_nonneg : ∀ a, 0 ≤ p a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hg_nonneg : ∀ a, 0 ≤ g a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hμ (b : β) :
      (∑' a : {a // f a = b}, p a) =
        (μ {ω | f (X ω) = b}).toReal := by
    have h := countable_law_event_real_tsum μ X hX {a : α | f a = b}
    change (∑' a : {a // f a = b},
      (μ (X ⁻¹' ({(a : α)} : Set α))).toReal) =
      (μ (X ⁻¹' ({a : α | f a = b} : Set α))).toReal at h
    simpa [p] using h
  have hν (b : β) :
      (∑' a : {a // f a = b}, g a) =
        (ν {ξ | f (Y ξ) = b}).toReal := by
    have h := countable_law_event_real_tsum ν Y hY {a : α | f a = b}
    change (∑' a : {a // f a = b},
      (ν (Y ⁻¹' ({(a : α)} : Set α))).toReal) =
      (ν (Y ⁻¹' ({a : α | f a = b} : Set α))).toReal at h
    simpa [g] using h
  have hcontract := countable_l1_pushforward_contraction f p g hp hg hp_nonneg hg_nonneg
  calc
    (∑ b : β,
        |(μ {ω | f (X ω) = b}).toReal -
          (ν {ξ | f (Y ξ) = b}).toReal|) =
        ∑ b : β,
          |(∑' a : {a // f a = b}, p a) -
            ∑' a : {a // f a = b}, g a| := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hμ b, hν b]
    _ ≤ ∑' a : α, |p a - g a| := hcontract
    _ = ∑' a : α,
        |(μ {ω | X ω = a}).toReal -
          (ν {ξ | Y ξ = a}).toReal| := by
      rfl


private def geomTwoParam : unitInterval :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

private lemma geomTwoParam_ne_zero : geomTwoParam ≠ 0 := by
  intro h
  have h' := congrArg (fun x : unitInterval => (x : ℝ)) h
  norm_num [geomTwoParam] at h'

/-- The positive-support `Geom(2)` law, obtained by shifting Mathlib's law. -/

lemma positiveGeomTwo_real_singleton (n : ℕ) :
    positiveGeomTwo.real {n + 1} = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [positiveGeomTwo, map_measureReal_apply (by fun_prop) (by measurability)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by
    ext x
    simp [Nat.succ_eq_add_one]
  rw [hpre]
  change (geometricMeasure
    (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : unitInterval)).real {n} = _
  have h := geometricMeasure_real_singleton
    (p := (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : unitInterval))
      (by intro h; have h' := congrArg (fun x : unitInterval => (x : ℝ)) h; norm_num at h') n
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num] at h
  simpa [pow_succ] using h

lemma positiveGeomTwo_singleton_zero : positiveGeomTwo {0} = 0 := by
  rw [positiveGeomTwo, Measure.map_apply (by fun_prop) (by measurability)]
  have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by
    ext x
    simp
  rw [hpre]
  simp

lemma positiveGeomTwo_singleton_succ (n : ℕ) :
    positiveGeomTwo {n + 1} = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  rw [positiveGeomTwo, Measure.map_apply (by fun_prop) (by measurability)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by
    ext x
    simp [Nat.succ_eq_add_one]
  rw [hpre]
  change (geometricMeasure
    (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : unitInterval)) {n} = _
  have h := geometricMeasure_singleton
    (p := (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ : unitInterval))
      (by intro h; have h' := congrArg (fun x : unitInterval => (x : ℝ)) h; norm_num at h') n
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num] at h
  simpa [pow_succ] using h

lemma positiveGeomTwoVector_real_singleton (t : ℕ) (a : Fin t → ℕ) :
    (positiveGeomTwoVector t).real {a} =
      if _ : ∀ i, 0 < a i then ∏ i, (1 / 2 : ℝ) ^ (a i) else 0 := by
  rw [positiveGeomTwoVector, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  by_cases h : ∀ i, 0 < a i
  · simp_rw [show ∀ i : Fin t, positiveGeomTwo {a i} =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (a i)) by
      intro i
      obtain ⟨n, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (h i))
      rw [hi]
      simpa [Nat.succ_eq_add_one] using positiveGeomTwo_singleton_succ n]
    have hnonneg : ∀ i : Fin t, 0 ≤ (1 / 2 : ℝ) ^ (a i) := fun i =>
      pow_nonneg (by norm_num) _
    simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
    simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hzero : a i = 0 := by omega
    have hiAtom : positiveGeomTwo {a i} = 0 := by
      rw [hzero]
      exact positiveGeomTwo_singleton_zero
    have hiReal : (positiveGeomTwo {a i}).toReal = 0 := by rw [hiAtom]; simp
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hiReal]
    simp [h]


theorem positiveGeomTwoVector_atom_of_pos
    (t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    (positiveGeomTwoVector t).real {a} = 1 / (2 : ℝ) ^ (∑ i, a i) := by
  rw [positiveGeomTwoVector_real_singleton]
  simp only [dif_pos ha]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [one_div_pow]

theorem positiveGeomTwoVector_atoms_summable (t : ℕ) :
    Summable (fun a : Fin t → ℕ => (positiveGeomTwoVector t).real {a}) := by
  simpa only [Set.preimage_id, measureReal_def] using
    countable_law_atoms_summable (positiveGeomTwoVector t) id measurable_id

theorem positiveGeomTwoVector_atoms_tsum (t : ℕ) :
    (∑' a : Fin t → ℕ, (positiveGeomTwoVector t).real {a}) = 1 := by
  simpa only [Set.preimage_id, measureReal_def] using
    countable_law_atoms_real_tsum (positiveGeomTwoVector t) id measurable_id




set_option autoImplicit false

open Nat

private lemma two_dvd_three_mul_add_one_of_odd {n : ℕ} (hn : Odd n) :
    2 ∣ 3 * n + 1 := by
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  refine ⟨3 * k + 2, ?_⟩
  omega

/-- Every positive Syracuse successor is positive. -/
theorem syracuse_step_pos {n : ℕ} (hn : 0 < n) : 0 < syracuseStep n := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.ordCompl_pos
  exact hpos.ne'

/-- Every positive Syracuse successor is odd. -/
theorem syracuse_step_odd {n : ℕ} (hn : 0 < n) : Odd (syracuseStep n) := by
  have hpos : 0 < 3 * n + 1 := by omega
  have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
    Nat.coprime_ordCompl Nat.prime_two hpos.ne'
  exact hcop.odd_of_left

/-- An odd positive input has a positive 2-adic exponent in its Syracuse numerator. -/
theorem syracuse_step_factorization_pos {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < (3 * n + 1).factorization 2 := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
  · exact hpos.ne'
  · exact two_dvd_three_mul_add_one_of_odd hodd

/-- The valuation-weighted Syracuse recurrence. -/
theorem syracuse_step_factorization_mul {n : ℕ} :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  simpa [syracuseStep] using Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/- The three adapter facts are often consumed together on positive odd inputs. -/
theorem syracuse_step_pos_odd_valuation {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < syracuseStep n ∧ Odd (syracuseStep n) ∧
      0 < (3 * n + 1).factorization 2 ∧
        2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact ⟨syracuse_step_pos hn, syracuse_step_odd hn,
    syracuse_step_factorization_pos hn hodd, syracuse_step_factorization_mul⟩




set_option autoImplicit false

open Nat

/-- Exactness of the exponent in `3 * n + 1` is equivalent to an odd
quotient, not merely to divisibility by the corresponding power of two. -/
theorem syracuse_factorization_two_iff_odd_quotient (n a : ℕ) :
    (3 * n + 1).factorization 2 = a ↔
      ∃ m : ℕ, Odd m ∧ 2 ^ a * m = 3 * n + 1 := by
  have hpos : 0 < 3 * n + 1 := by omega
  constructor
  · intro ha
    have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
      Nat.coprime_ordCompl Nat.prime_two hpos.ne'
    refine ⟨syracuseStep n, ?_, ?_⟩
    · simpa [syracuseStep] using hcop.odd_of_left
    · simpa [ha] using (syracuse_step_factorization_mul (n := n))
  · rintro ⟨m, hmodd, hmul⟩
    have hpowdvd : 2 ^ a ∣ 3 * n + 1 := ⟨m, hmul.symm⟩
    have hle : a ≤ (3 * n + 1).factorization 2 := by
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mp hpowdvd
    have hnotdvd : ¬2 ^ (a + 1) ∣ 3 * n + 1 := by
      intro hdiv
      rcases hdiv with ⟨k, hk⟩
      have hcancel : 2 * k = m := by
        apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
        calc
          2 ^ a * (2 * k) = 2 ^ (a + 1) * k := by
            simp [pow_succ, Nat.mul_assoc]
          _ = 3 * n + 1 := hk.symm
          _ = 2 ^ a * m := hmul.symm
      obtain ⟨j, hj⟩ := hmodd
      omega
    have hnotle : ¬a + 1 ≤ (3 * n + 1).factorization 2 := by
      intro h
      apply hnotdvd
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mpr h
    omega


/-- The exact exponent used by the `i`-th accelerated Syracuse step. -/
def syracuseExponent (N i : ℕ) : ℕ :=
  (3 * (syracuseStep^[i]) N + 1).factorization 2

/-- Positive oddness propagates through every forward Syracuse iterate. -/
theorem syracuse_iterate_pos_odd (N : ℕ) (hN : 0 < N) (hodd : Odd N) (i : ℕ) :
    0 < (syracuseStep^[i]) N ∧ Odd ((syracuseStep^[i]) N) := by
  induction i with
  | zero =>
      simpa using And.intro hN hodd
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨syracuse_step_pos ih.1, syracuse_step_odd ih.1⟩

/-- Every exponent in the positive odd Syracuse orbit is positive. -/
theorem syracuse_exponent_pos (N i : ℕ) (hN : 0 < N) (hodd : Odd N) :
    0 < syracuseExponent N i := by
  unfold syracuseExponent
  obtain ⟨hi_pos, hi_odd⟩ := syracuse_iterate_pos_odd N hN hodd i
  exact syracuse_step_factorization_pos hi_pos hi_odd

/-- Each consecutive pair in the orbit satisfies the exact valuation recurrence. -/
theorem syracuse_exponent_chain (N i : ℕ) :
    2 ^ syracuseExponent N i * (syracuseStep^[i + 1]) N =
      3 * (syracuseStep^[i]) N + 1 := by
  simpa [syracuseExponent, Function.iterate_succ_apply'] using
    (syracuse_step_factorization_mul (n := (syracuseStep^[i]) N))

/-- A positive threshold crossed by a finite partial sum has a first crossing. -/
theorem exists_first_crossing (a : ℕ → ℕ) :
    ∀ (t q : ℕ), 0 < q → q ≤ ∑ i ∈ Finset.range t, a i →
      ∃ k < t,
        (∑ i ∈ Finset.range k, a i) < q ∧
          q ≤ (∑ i ∈ Finset.range k, a i) + a k
  | 0, q, hq, hsum => by
      simp at hsum
      omega
  | t + 1, q, hq, hsum => by
      by_cases hprefix : q ≤ ∑ i ∈ Finset.range t, a i
      · obtain ⟨k, hkt, hlt, hcross⟩ := exists_first_crossing a t q hq hprefix
        exact ⟨k, lt_trans hkt (Nat.lt_succ_self t), hlt, hcross⟩
      · have hlt : (∑ i ∈ Finset.range t, a i) < q := Nat.lt_of_not_ge hprefix
        refine ⟨t, Nat.lt_succ_self t, hlt, ?_⟩
        simpa [Finset.sum_range_succ] using hsum


def syracuseAffineNumerator (as : List ℕ) (N : ℕ) : ℕ :=
  3 ^ as.length * N + syracuseAffineConstant as

def syracuseExactValuationPrefix (N : ℕ) : List ℕ → Prop
  | [] => True
  | a :: as => syracuseExponent N 0 = a ∧
      syracuseExactValuationPrefix (syracuseStep N) as

lemma syracuseAffineNumerator_shift (as : List ℕ) (N : ℕ) :
    syracuseAffineNumerator as N =
      3 ^ as.length * N + syracuseAffineNumerator as 0 := by
  simp [syracuseAffineNumerator]

lemma syracuseAffineNumerator_cons (a : ℕ) (as : List ℕ) (N : ℕ) :
    syracuseAffineNumerator (a :: as) N =
      3 ^ as.length * (3 * N + 1) +
        2 ^ a * syracuseAffineNumerator as 0 := by
  simp [syracuseAffineNumerator, syracuseAffineConstant, pow_succ]
  ring

lemma syracuseAffineConstant_cons_odd (a : ℕ) (as : List ℕ) (ha : 0 < a) :
    Odd (syracuseAffineConstant (a :: as)) := by
  simp only [syracuseAffineConstant]
  apply Odd.add_even
  · exact Odd.pow (by decide : Odd (3 : ℕ))
  · exact ((show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
      (by omega : a ≠ 0)).mul_right _

lemma syracuse_exponent_step_shift (N i : ℕ) :
    syracuseExponent (syracuseStep N) i = syracuseExponent N (i + 1) := by
  simp only [syracuseExponent]
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem syracuse_exact_valuation_prefix_iff
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) (as : List ℕ)
    (ha : ∀ a ∈ as, 0 < a) :
    syracuseExactValuationPrefix N as ↔
      ∃ m : ℕ, Odd m ∧
        2 ^ as.sum * m = syracuseAffineNumerator as N := by
  induction as generalizing N with
  | nil =>
      constructor
      · intro _
        exact ⟨N, hodd, by simp [syracuseAffineNumerator, syracuseAffineConstant]⟩
      · rintro ⟨m, hm, _⟩
        trivial
  | cons a as ih =>
      have ha0 : 0 < a := ha a (by simp)
      have harest : ∀ b ∈ as, 0 < b := by
        intro b hb
        exact ha b (by simp [hb])
      constructor
      · rintro ⟨hhead, htail⟩
        have hstep_pos : 0 < syracuseStep N := syracuse_step_pos hN
        have hstep_odd : Odd (syracuseStep N) := syracuse_step_odd hN
        obtain ⟨m, hm, htailEq⟩ :=
          (ih (N := syracuseStep N) hstep_pos hstep_odd harest).mp htail
        have hchain : 2 ^ a * syracuseStep N = 3 * N + 1 := by
          calc
            2 ^ a * syracuseStep N =
                2 ^ syracuseExponent N 0 * syracuseStep N := by rw [hhead]
            _ = 3 * N + 1 := by simpa using syracuse_exponent_chain N 0
        refine ⟨m, hm, ?_⟩
        calc
          2 ^ (a :: as).sum * m =
              2 ^ a * (2 ^ as.sum * m) := by
                simp [List.sum_cons, pow_add]
                ring
          _ = 2 ^ a * syracuseAffineNumerator as (syracuseStep N) := by
                rw [htailEq]
          _ = 2 ^ a *
                (3 ^ as.length * syracuseStep N +
                  syracuseAffineNumerator as 0) := by
                rw [syracuseAffineNumerator_shift]
          _ = 3 ^ as.length * (3 * N + 1) +
                2 ^ a * syracuseAffineNumerator as 0 := by
                rw [← hchain]
                ring
          _ = syracuseAffineNumerator (a :: as) N := by
                symm
                exact syracuseAffineNumerator_cons a as N
      · rintro ⟨m, hm, hEq⟩
        have hEq' :
            2 ^ (a + as.sum) * m = syracuseAffineNumerator (a :: as) N := by
          simpa [List.sum_cons] using hEq
        let x : ℕ := 2 ^ as.sum * m
        have hAeq : syracuseAffineNumerator (a :: as) N = 2 ^ a * x := by
          calc
            syracuseAffineNumerator (a :: as) N = 2 ^ (a + as.sum) * m := hEq'.symm
            _ = 2 ^ a * x := by
              simp [x, pow_add]
              ring
        have hAdiv : 2 ^ a ∣ syracuseAffineNumerator (a :: as) N :=
          ⟨x, hAeq⟩
        have hsumdiv :
            2 ^ a ∣ 3 ^ as.length * (3 * N + 1) +
              2 ^ a * syracuseAffineNumerator as 0 := by
          rw [syracuseAffineNumerator_cons] at hAdiv
          exact hAdiv
        have hCdiv : 2 ^ a ∣ 2 ^ a * syracuseAffineNumerator as 0 :=
          dvd_mul_right _ _
        have hsumdiv' :
            2 ^ a ∣ 2 ^ a * syracuseAffineNumerator as 0 +
              3 ^ as.length * (3 * N + 1) := by
          simpa [Nat.add_comm] using hsumdiv
        have hXdiv : 2 ^ a ∣ 3 ^ as.length * (3 * N + 1) := by
          simpa using (Nat.dvd_add_iff_right hCdiv).mpr hsumdiv'
        have hcop : Nat.Coprime (2 ^ a) (3 ^ as.length) := by
          exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)
        have hheadDiv : 2 ^ a ∣ 3 * N + 1 :=
          (hcop.dvd_mul_left).mp hXdiv
        obtain ⟨y, hy⟩ := hheadDiv
        have hy_pos : 0 < y := by
          have hy_ne : y ≠ 0 := by
            intro hy0
            subst y
            simp at hy
          exact Nat.pos_of_ne_zero hy_ne
        have hrel : x = 3 ^ as.length * y + syracuseAffineNumerator as 0 := by
          apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
          calc
            2 ^ a * x = syracuseAffineNumerator (a :: as) N := hAeq.symm
            _ = 3 ^ as.length * (3 * N + 1) +
                2 ^ a * syracuseAffineNumerator as 0 :=
                  syracuseAffineNumerator_cons a as N
            _ = 3 ^ as.length * (2 ^ a * y) +
                2 ^ a * syracuseAffineNumerator as 0 := by rw [hy]
            _ = 2 ^ a *
                (3 ^ as.length * y + syracuseAffineNumerator as 0) := by
                  ring
        have hy_odd : Odd y := by
          cases as with
          | nil =>
              have hy_eq : y = m := by
                calc
                  y = x := by
                    simpa [syracuseAffineNumerator, syracuseAffineConstant] using hrel.symm
                  _ = m := by simp [x]
              simpa [hy_eq] using hm
          | cons b bs =>
              have hb : 0 < b := harest b (by simp)
              have hsum_pos : 0 < (b :: bs).sum := by
                simp [List.sum_cons]
                omega
              have hx_even : Even x := by
                have hp : Even (2 ^ (b :: bs).sum) :=
                  (show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
                    (by omega : (b :: bs).sum ≠ 0)
                exact hp.mul_right m
              have hCodd : Odd (syracuseAffineConstant (b :: bs)) :=
                syracuseAffineConstant_cons_odd b bs hb
              have hCodd' : Odd (syracuseAffineNumerator (b :: bs) 0) := by
                simpa [syracuseAffineNumerator] using hCodd
              have hadd_even :
                  Even (3 ^ (b :: bs).length * y +
                    syracuseAffineNumerator (b :: bs) 0) := by
                rw [← hrel]
                exact hx_even
              have hprod_odd : Odd (3 ^ (b :: bs).length * y) :=
                (even_add').mp hadd_even |>.mpr hCodd'
              exact hprod_odd.of_mul_right
        have hhead : syracuseExponent N 0 = a := by
          simpa [syracuseExponent] using
            (syracuse_factorization_two_iff_odd_quotient N a).mpr
              ⟨y, hy_odd, hy.symm⟩
        have hy_step : y = syracuseStep N := by
          apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
          calc
            2 ^ a * y = 3 * N + 1 := hy.symm
            _ = 2 ^ a * syracuseStep N := by
              rw [← hhead]
              simpa using (syracuse_exponent_chain N 0).symm
        have htailEq :
            2 ^ as.sum * m = syracuseAffineNumerator as y := by
          calc
            2 ^ as.sum * m = x := by rfl
            _ = 3 ^ as.length * y + syracuseAffineNumerator as 0 := hrel
            _ = syracuseAffineNumerator as y :=
              (syracuseAffineNumerator_shift as y).symm
        have htail :=
          (ih (N := y) hy_pos hy_odd harest).mpr ⟨m, hm, htailEq⟩
        exact ⟨hhead, by simpa [hy_step] using htail⟩

/-- Finite-function adapter for the list-inductive characterization. -/
theorem syracuse_exact_valuation_prefix_fin_iff
    (N t : ℕ) (hN : 0 < N) (hodd : Odd N)
    (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    syracuseExactValuationPrefix N (List.ofFn a) ↔
      ∃ m : ℕ, Odd m ∧
        2 ^ (∑ i, a i) * m = syracuseAffineNumerator (List.ofFn a) N := by
  have hlist : ∀ b ∈ List.ofFn a, 0 < b := by
    rw [List.forall_mem_ofFn_iff]
    exact ha
  have h := syracuse_exact_valuation_prefix_iff N hN hodd (List.ofFn a) hlist
  simpa [List.sum_ofFn] using h


/- This helper identifies the quotient in the affine identity with the actual
   endpoint of the Syracuse iterate, rather than merely asserting existence of
   an odd quotient. -/
theorem syracuse_iterate_affine_numerator (N t : ℕ) :
    2 ^ (∑ i : Fin t, syracuseExponent N i) * (syracuseStep^[t]) N =
      syracuseAffineNumerator
        (List.ofFn (fun i : Fin t => syracuseExponent N i)) N := by
  induction t generalizing N with
  | zero =>
      simp [syracuseAffineNumerator, syracuseAffineConstant]
  | succ t ih =>
      let tail : Fin t → ℕ := fun i => syracuseExponent N i.succ
      have hvec :
          (fun i : Fin (t + 1) => syracuseExponent N i) =
            Fin.cons (syracuseExponent N 0) tail := by
        funext i
        exact Fin.cases rfl (fun j => rfl) i
      have htail :
          (fun i : Fin t => syracuseExponent (syracuseStep N) i) = tail := by
        funext i
        exact syracuse_exponent_step_shift N i
      have hih := ih (N := syracuseStep N)
      rw [hvec, List.ofFn_cons]
      rw [Fin.sum_univ_succ]
      rw [Function.iterate_succ_apply]
      rw [htail] at hih
      have hih' :
          2 ^ (∑ i, tail i) * (syracuseStep^[t]) (syracuseStep N) =
            3 ^ t * syracuseStep N + syracuseAffineNumerator (List.ofFn tail) 0 := by
        rw [syracuseAffineNumerator_shift] at hih
        simpa only [List.length_ofFn] using hih
      have hchain :
          2 ^ syracuseExponent N 0 * syracuseStep N = 3 * N + 1 :=
        syracuse_exponent_chain N 0
      calc
        2 ^ (syracuseExponent N 0 + ∑ i, tail i) *
              (syracuseStep^[t]) (syracuseStep N) =
            2 ^ syracuseExponent N 0 *
              (2 ^ (∑ i, tail i) * (syracuseStep^[t]) (syracuseStep N)) := by
                rw [pow_add]
                ring
        _ = 2 ^ syracuseExponent N 0 *
              (3 ^ t * syracuseStep N + syracuseAffineNumerator (List.ofFn tail) 0) := by
                rw [hih']
        _ = 3 ^ t * (3 * N + 1) +
              2 ^ syracuseExponent N 0 * syracuseAffineNumerator (List.ofFn tail) 0 := by
                calc
                  _ = 3 ^ t *
                        (2 ^ syracuseExponent N 0 * syracuseStep N) +
                        2 ^ syracuseExponent N 0 *
                          syracuseAffineNumerator (List.ofFn tail) 0 := by ring
                  _ = _ := by rw [hchain]
        _ = syracuseAffineNumerator
              (syracuseExponent N 0 :: List.ofFn tail) N := by
                rw [syracuseAffineNumerator_cons]
                simp [syracuseAffineNumerator, List.length_ofFn]

theorem syracuse_iterate_mod_three_pow_eq_offset
    (N t k : ℕ) (_hN : 0 < N) (_hodd : Odd N) (hkt : k ≤ t) :
    ((syracuseStep^[t]) N : ZMod (3 ^ k)) =
      syracuseOffsetMod t k (fun i : Fin t => syracuseExponent N i) := by
  have haff := syracuse_iterate_affine_numerator N t
  by_cases hk : k = 0
  · subst k
    have hsub : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    exact hsub.elim _ _
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hzero :
      ((3 ^ t * N : ℕ) : ZMod (3 ^ k)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 3 hkt) N
  have hnotdvd : ¬ 3 ∣ 2 ^ (∑ i : Fin t, syracuseExponent N i) := by
    intro hdvd
    have hthree : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at hthree
  have hunit : IsUnit
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) := by
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_three hkpos]
    exact hnotdvd
  have hcast :
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) ≠ 0 := by
    intro hz
    have hdvd : 3 ^ k ∣ 2 ^ (∑ i : Fin t, syracuseExponent N i) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact hnotdvd (dvd_trans (dvd_pow_self 3 hk) hdvd)
  have haffZ := congrArg (fun x : ℕ => (x : ZMod (3 ^ k))) haff
  have hmod :
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
          ((syracuseStep^[t]) N : ZMod (3 ^ k)) =
        (syracuseAffineConstant
          (List.ofFn (fun i : Fin t => syracuseExponent N i)) : ZMod (3 ^ k)) := by
    calc
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
            ((syracuseStep^[t]) N : ZMod (3 ^ k)) =
          (syracuseAffineNumerator
            (List.ofFn (fun i : Fin t => syracuseExponent N i)) N : ZMod (3 ^ k)) := by
              simpa only [Nat.cast_mul] using haffZ
      _ = ((3 ^ t * N : ℕ) : ZMod (3 ^ k)) +
            (syracuseAffineConstant
              (List.ofFn (fun i : Fin t => syracuseExponent N i)) : ZMod (3 ^ k)) := by
              simp [syracuseAffineNumerator, List.length_ofFn, Nat.cast_add, Nat.cast_mul]
      _ = (syracuseAffineConstant
            (List.ofFn (fun i : Fin t => syracuseExponent N i)) : ZMod (3 ^ k)) := by
              rw [hzero, zero_add]
  have hoff :
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
          syracuseOffsetMod t k (fun i : Fin t => syracuseExponent N i) =
        (syracuseAffineConstant
          (List.ofFn (fun i : Fin t => syracuseExponent N i)) : ZMod (3 ^ k)) := by
    rw [syracuseOffsetMod]
    calc
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
            ((syracuseAffineConstant
              (List.ofFn (fun i : Fin t => syracuseExponent N i)) : ZMod (3 ^ k)) *
              ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k))⁻¹) =
          (syracuseAffineConstant
            (List.ofFn (fun i : Fin t => syracuseExponent N i)) : ZMod (3 ^ k)) *
            (((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
              ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k))⁻¹) := by
                ring
      _ = _ := by
        have hcancel :
            ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
                ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k))⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ hunit
        rw [hcancel, mul_one]
  have hprod :
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
          ((syracuseStep^[t]) N : ZMod (3 ^ k)) =
        ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
          syracuseOffsetMod t k (fun i : Fin t => syracuseExponent N i) :=
    hmod.trans hoff.symm
  have hleft :
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k))⁻¹ *
          (((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
            ((syracuseStep^[t]) N : ZMod (3 ^ k))) =
        ((syracuseStep^[t]) N : ZMod (3 ^ k)) := by
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul]
  have hright :
      ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k))⁻¹ *
          (((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k)) *
            syracuseOffsetMod t k (fun i : Fin t => syracuseExponent N i)) =
        syracuseOffsetMod t k (fun i : Fin t => syracuseExponent N i) := by
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ hunit, one_mul]
  exact hleft.symm.trans
    ((congrArg
      (fun x : ZMod (3 ^ k) =>
        ((2 ^ (∑ i : Fin t, syracuseExponent N i) : ℕ) : ZMod (3 ^ k))⁻¹ * x)
      hprod).trans hright)


def syracuseValuationVector {Ω : Type*} (t : ℕ) (N : Ω → ℕ) (ω : Ω) : Fin t → ℕ :=
  fun i => syracuseExponent (N ω) i

theorem measurable_syracuseValuationVector
    {Ω : Type*} [MeasurableSpace Ω] (t : ℕ) (N : Ω → ℕ)
    (hN : Measurable N) : Measurable (syracuseValuationVector t N) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_countable (fun n : ℕ => syracuseExponent n i)).comp hN


open scoped Classical in
theorem syracuse_offset_law_l1_contraction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N)
    (hAE : ∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω))
    (t k : ℕ) (hkt : k ≤ t) :
    (∑ b : ZMod (3 ^ k),
        |(μ {ω |
            ((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b}).toReal -
          (positiveGeomTwoVector t).real
            {a | syracuseOffsetMod t k a = b}|) ≤
      ∑' a : Fin t → ℕ,
        |(μ {ω | ∀ i : Fin t,
            (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal -
          (if ∀ i : Fin t, 0 < a i then
            1 / (2 : ℝ) ^ (∑ i, a i) else 0)| := by
  let f : (Fin t → ℕ) → ZMod (3 ^ k) := syracuseOffsetMod t k
  have hpush := countable_law_pushforward_l1
    (μ := μ) (ν := positiveGeomTwoVector t)
    (X := syracuseValuationVector t N) (Y := id) (f := f)
    (hX := measurable_syracuseValuationVector t N hN) (hY := measurable_id)
  have hactual (b : ZMod (3 ^ k)) :
      (μ {ω | f (syracuseValuationVector t N ω) = b}).toReal =
        (μ {ω |
          ((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b}).toReal := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hAE] with ω hω
    change (f (syracuseValuationVector t N ω) = b) =
      (((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b)
    apply propext
    dsimp [f, syracuseValuationVector]
    rw [syracuse_iterate_mod_three_pow_eq_offset (N ω) t k hω.1 hω.2 hkt]
    rfl
  have hvector_to_factor :
      (∑' a : Fin t → ℕ,
        |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
          (positiveGeomTwoVector t).real {a}|) =
        ∑' a : Fin t → ℕ,
          |(μ {ω | ∀ i : Fin t,
              (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal -
            (if ∀ i : Fin t, 0 < a i then
              1 / (2 : ℝ) ^ (∑ i, a i) else 0)| := by
    apply tsum_congr
    intro a
    have hmodel : (positiveGeomTwoVector t).real {a} =
        if ∀ i : Fin t, 0 < a i then 1 / (2 : ℝ) ^ (∑ i, a i) else 0 := by
      by_cases ha : ∀ i : Fin t, 0 < a i
      · rw [if_pos ha]
        exact positiveGeomTwoVector_atom_of_pos t a ha
      · simp [positiveGeomTwoVector_real_singleton, ha]
    have hset :
        {ω | ∀ i : Fin t,
          (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i} =
          {ω | syracuseValuationVector t N ω = a} := by
      ext ω
      constructor
      · intro hcoords
        funext i
        exact hcoords i
      · intro hcoords i
        exact congrFun hcoords i
    rw [hmodel, hset]
  calc
    (∑ b : ZMod (3 ^ k),
        |(μ {ω |
            ((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b}).toReal -
          (positiveGeomTwoVector t).real
            {a | syracuseOffsetMod t k a = b}|) =
        ∑ b : ZMod (3 ^ k),
          |(μ {ω | f (syracuseValuationVector t N ω) = b}).toReal -
            (positiveGeomTwoVector t).real
              {a | f a = b}| := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hactual b]
    _ ≤ ∑' a : Fin t → ℕ,
        |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
          (positiveGeomTwoVector t).real {a}| := by
      simpa [f, measureReal_def] using hpush
    _ = ∑' a : Fin t → ℕ,
        |(μ {ω | ∀ i : Fin t,
            (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal -
          (if ∀ i : Fin t, 0 < a i then
            1 / (2 : ℝ) ^ (∑ i, a i) else 0)| := hvector_to_factor


end CollatzOffsetPackage

open CollatzOffsetPackage

theorem solution
    (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ A d : ℝ, 0 < A ∧ 0 < d ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ),
        Measurable N → (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) →
        ∀ q t k : ℕ, (2 + c) * (t : ℝ) ≤ (q : ℝ) →
          (∑ r : Fin (2 ^ q),
            |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
              (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤ K / (2 : ℝ) ^ q) →
          k ≤ t →
          (∑ b : ZMod (3 ^ k),
            |(μ {ω |
                ((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b}).toReal -
              (positiveGeomTwoVector t).real
                {a | syracuseOffsetMod t k a = b}|) ≤
            A * Real.exp (-d * (t : ℝ)) := by
  obtain ⟨A, d, hA, hd, hsource⟩ :=
    syracuse_valuation_joint_geometric c K hc hK
  refine ⟨A, d, hA, hd, ?_⟩
  intro Ω _ μ _ N hN hAE q t k hqt hL1 hkt
  calc
    (∑ b : ZMod (3 ^ k),
        |(μ {ω |
            ((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b}).toReal -
          (positiveGeomTwoVector t).real
            {a | syracuseOffsetMod t k a = b}|) ≤
        ∑' a : Fin t → ℕ,
          |(μ {ω | ∀ i : Fin t,
              (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal -
            (if ∀ i : Fin t, 0 < a i then
              1 / (2 : ℝ) ^ (∑ i, a i) else 0)| :=
      syracuse_offset_law_l1_contraction μ N hN hAE t k hkt
    _ ≤ A * Real.exp (-d * (t : ℝ)) :=
      hsource μ N hN hAE q t hqt hL1
