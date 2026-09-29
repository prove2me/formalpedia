-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_relative_degree_package
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:16:37.43118+00:00
-- url     : https://prove2.me/submissions/3278fd21-a38b-4b67-8e80-a5e559c8de89

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_uniform_cyclic_mode_degrees
import Theorems.Thm_mme_stothers_phi233_cyclic_star_ratio

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- The concrete phi_233 cyclic families satisfy the uniform degree,
target-factorization, and relative-degree hypotheses of the sharp type-2
extraction theorem. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta)
    [DecidableEq (MME.StothersFourth.Phi233.CyclicModeWord N)]
    (R : ℝ) (hR : 0 ≤ R)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    let D := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l}
    let Dstar := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta // b.1.1 l = a.1.1 l}
    let V := ∏ l : Fin 3,
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta l s).factorial)
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.ambientFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card ≤ D) ∧
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = Dstar) ∧
    ((MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card : ℝ) = (V : ℝ) * (Dstar : ℝ) ∧
    (D : ℝ) ≤ R ^ 3 * (Dstar : ℝ) := by
  classical
  let D := ∏ l : Fin 3,
    Nat.card
      {b : MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta // b.1 l = a.1.1 l}
  let Dstar := ∏ l : Fin 3,
    Nat.card
      {b : MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta // b.1.1 l = a.1.1 l}
  let V := ∏ l : Fin 3,
    ((2 * N).factorial /
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s).factorial)
  have hdegrees := mme_stothers_phi233_uniform_cyclic_mode_degrees
    N alpha beta gamma delta hsum a
  change
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.ambientFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = D) ∧
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = Dstar) ∧
    (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card = V * Dstar at hdegrees
  rcases hdegrees with ⟨hambient, htarget, hcard⟩
  have hdegreeRatio : (D : ℝ) ≤ R ^ 3 * (Dstar : ℝ) := by
    simpa only [D, Dstar, Nat.cast_prod] using
      (mme_stothers_phi233_cyclic_star_ratio
        N alpha beta gamma delta hsum a R hR hratio)
  refine ⟨?_, htarget, ?_, hdegreeRatio⟩
  · intro i e he
    exact (hambient i e he).le
  · exact_mod_cast hcard
