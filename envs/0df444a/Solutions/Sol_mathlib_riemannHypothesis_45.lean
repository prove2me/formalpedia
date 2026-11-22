-- Prove2me | solution 45 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:02.47382+00:00
-- url     : https://prove2.me/submissions/c18c645f-c432-47ef-8f87-31292c079a66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_mobius_character_and_progression_bounds_above_record
import Theorems.Thm_GRH_sharp_mobius_character_power_bound_below_record
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

-- Step 1: `GRH.sharp_mobius_character_power_bound_below_record` implies `GRH.sharp_mobius_character_power_bound` (accepted reduction of `GRH.sharp_mobius_character_power_bound`).
section

open Filter Asymptotics

/-- Proof sketch for `GRH.sharp_mobius_character_power_bound`.

    Split the exponent range at the verified zero-free record `0.8749570698`.
    Above the record the character bound is the first conjunct of the Proved
    record theorem; at or below it we invoke the strictly weaker child carrying
    `hcap : σ ≤ 0.8749570698`. -/
theorem GRH.sharp_mobius_character_power_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by
  by_cases hrec : (0.8749570698 : ℝ) < σ
  · -- Above the record: first conjunct of the record theorem, instantiated at χ.
    exact (GRH.mobius_character_and_progression_bounds_above_record q σ hrec).1 χ
  · -- At or below the record: the remaining open child.
    exact GRH.sharp_mobius_character_power_bound_below_record q χ σ hhalf hone (le_of_not_gt hrec)

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
