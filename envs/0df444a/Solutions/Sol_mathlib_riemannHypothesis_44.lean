-- Prove2me | solution 44 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:00.807841+00:00
-- url     : https://prove2.me/submissions/a971d741-da64-4a5d-819b-bbb5cf456289
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_moebius_partial_sum_reduced_progression_power_bound
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

-- Step 1: `GRH.moebius_partial_sum_reduced_progression_power_bound` implies `GRH.sharp_mobius_character_power_bound` (accepted reduction of `GRH.sharp_mobius_character_power_bound`).
section

set_option autoImplicit false

open Filter Asymptotics
open scoped BigOperators

private lemma sharp_progression_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (H : ∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ Finset.range (n+1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
        C * ((n : ℝ) + 1)^σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖∑ k ∈ Finset.range (n+1), χ (k : ZMod q) * (ArithmeticFunction.moebius k : ℂ)‖ ≤
        C * ((n : ℝ) + 1)^σ := by
  classical
  let A (a : ZMod q) (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1),
    if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0
  have hterms (a : ZMod q) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖χ a * (A a n : ℂ)‖ ≤ C * ((n : ℝ) + 1)^σ := by
    by_cases ha : IsUnit a
    · obtain ⟨C, hC, hc⟩ := H a ha
      refine ⟨C, hC, fun n => ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact ((mul_le_mul_of_nonneg_right (χ.norm_le_one a) (abs_nonneg (A a n))).trans_eq
        (one_mul _)).trans (hc n)
    · exact ⟨0, le_rfl, fun n => by simp [χ.map_nonunit ha]⟩
  choose C hC hc using hterms
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ => hC a), fun n => ?_⟩
  have heq : ∑ k ∈ Finset.range (n+1), χ (k : ZMod q) * (ArithmeticFunction.moebius k : ℂ) =
      ∑ a, χ a * (A a n : ℂ) := by
    simp only [A, Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero,
      Complex.ofReal_intCast, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by simp
  rw [heq, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hc a n)

theorem GRH.sharp_mobius_character_power_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n+1),
      χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by
  obtain ⟨C, hC, hsum⟩ := sharp_progression_bound q χ σ
    (fun a ha => GRH.moebius_partial_sum_reduced_progression_power_bound q a ha σ hhalf hone)
  refine isBigO_iff.mpr ⟨C * 2 ^ σ, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 ≤ (n : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn₀ _)]
  calc
    _ ≤ C * ((n : ℝ) + 1) ^ σ := hsum n
    _ ≤ C * (2 * (n : ℝ)) ^ σ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn₀, mul_assoc]

end

-- Step 2: `GRH.sharp_mobius_character_power_bound` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  intro s hz htriv hone
  have : Subsingleton (ZMod 1) := inferInstanceAs (Subsingleton (Fin 1))
  have hsum : ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1),
          (1 : DirichletCharacter ℂ 1) (k : ZMod 1) * (ArithmeticFunction.moebius k : ℂ) =
        ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ) := by
    intro n
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc, not_and, not_le] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp
    · intro k _
      rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
  have key : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → 1 - σ ≤ s.re ∧ s.re ≤ σ := by
    intro σ h1 h2
    have h := (GRH.sharp_mobius_character_power_bound 1 (1 : DirichletCharacter ℂ 1) σ h1 h2).congr_left
      hsum
    exact nontrivial_zero_strip_of_moebius_summatory_power_bound (r := σ) (by linarith) h hz htriv hone
  have h34 := key (3 / 4) (by norm_num) (by norm_num)
  have hle : s.re ≤ 1 / 2 := by
    by_contra hlt
    push_neg at hlt
    have := (key ((1 / 2 + s.re) / 2) (by linarith) (by linarith [h34.2])).2
    linarith
  have hge : 1 / 2 ≤ s.re := by
    by_contra hlt
    push_neg at hlt
    have := (key (1 - (s.re + 1 / 2) / 2) (by linarith [h34.1]) (by linarith [h34.1])).1
    linarith
  exact le_antisymm hle hge

end
