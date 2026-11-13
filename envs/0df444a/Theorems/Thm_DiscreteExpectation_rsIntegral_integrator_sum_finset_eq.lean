-- Prove2me | Theorems.Thm_DiscreteExpectation_rsIntegral_integrator_sum_finset_eq
-- name    : DiscreteExpectation.rsIntegral_integrator_sum_finset_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:12:48.136048+00:00
-- url     : https://prove2.me/theorems/700832f9-7601-45d3-8f02-2259799c9082
-- title:
--   ProbabilityTheory_chapter_01_def_1_3_F001: DiscreteExpectation.rsIntegral_integrator_sum_finset_eq
-- statement:
--   Source theorem `DiscreteExpectation.rsIntegral_integrator_sum_finset_eq` extracted from `ProbabilityTheory.chapter_01.def_1_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
noncomputable section
end
noncomputable section DiscreteExpectation
namespace DiscreteExpectation

private lemma sourceHypotheses_zero_integrator (a b : ℝ) (hab : a < b) :
    SourceHypotheses a b (fun x => x) (fun _ => 0) := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩
  · intro x hx y hy hxy; rfl

private theorem taggedCommonLimit_zero (a b : ℝ) (hab : a < b) :
    TaggedCommonLimit a b (fun x => x) (fun _ => 0) 0 := by
  refine ⟨sourceHypotheses_zero_integrator a b hab, ?_⟩
  intro eps heps
  refine ⟨1, zero_lt_one, ?_⟩
  intro P tags htags hmesh
  have hS : taggedSum P tags (fun x => x) (fun x => 0) = 0 := by
    unfold taggedSum; apply Finset.sum_eq_zero; intro i _; ring
  rw [hS, sub_zero, abs_zero]
  exact heps

private theorem rsIntegrable_zero (a b : ℝ) (hab : a < b) :
    RSIntegrable (fun x => x) (fun _ => 0) a b := by
  -- 1. Construct the Darboux upper/lower common limit (evaluating to 0)
  have h_ul : UpperLowerCommonLimit a b (fun x => x) (fun x => 0) 0 := by
    refine ⟨sourceHypotheses_zero_integrator a b hab, ?_⟩
    intro eps heps
    -- Since the sum is exactly 0, any delta works. We arbitrarily pick 1.
    refine ⟨1, zero_lt_one, ?_⟩
    intro P _hmesh

    have h_up : upperSum P (fun x => x) (fun x => 0) = 0 := by
      unfold upperSum
      apply Finset.sum_eq_zero
      intro i _
      ring

    have h_low : lowerSum P (fun x => x) (fun x => 0) = 0 := by
      unfold lowerSum
      apply Finset.sum_eq_zero
      intro i _
      ring

    -- Substitute the sums and evaluate |0 - 0| < eps
    rw [h_up, h_low, sub_zero, abs_zero]
    exact ⟨heps, heps⟩

  -- 2. Fetch the Tagged limit (which we already proved evaluates to 0)
  have h_tg : TaggedCommonLimit a b (fun x => x) (fun x => 0) 0 :=
    taggedCommonLimit_zero a b hab

  -- 3. Package them into the `RSIntegralWitness` structure.
  -- The existential `Nonempty` wrapper is satisfied by `⟨...⟩`
  exact ⟨⟨0, h_ul, h_tg⟩⟩

/-- Integrability of a finite sum of integrators -/
private theorem rsIntegrable_integrator_sum_finset {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :  -- Changed to ∀ i
    RSIntegrable (fun x => x) (fun x => ∑ i ∈ s, α i x) a b := by
  induction' s using Finset.induction_on with i s' hi ih
  · simp only [Finset.sum_empty]
    exact rsIntegrable_zero a b hab
  · simp only [Finset.sum_insert hi]
    -- Now we just pass `h i` directly!
    exact rsIntegrable_integrator_add (h i) ih

theorem rsIntegral_integrator_sum_finset_eq {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :
    rsIntegral (fun x => x) (fun x => ∑ i ∈ s, α i x) a b
      (rsIntegrable_integrator_sum_finset s α a b hab h) =
    ∑ i ∈ s, rsIntegral (fun x => x) (α i) a b (h i) := by
  sorry
end DiscreteExpectation
end DiscreteExpectation
