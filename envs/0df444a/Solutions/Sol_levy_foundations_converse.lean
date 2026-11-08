-- Prove2me | solution 1 for levy_foundations_converse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:46:05.258404+00:00
-- url     : https://prove2.me/submissions/60cc8bf5-b4b3-471b-8131-3502be1018bf

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Theorems.Thm_ProbabilityTheory_levyKhintchine_converse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

/-- Source theorem transfer, including equality of the two convolution-power recursions. -/
theorem solution (T : LevyFoundations.LevyKhintchineTriple) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      LevyFoundations.isInfinitelyDivisible μ ∧
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  let V : LevyKhintchineTriple :=
    ⟨T.drift, T.gaussianVariance, T.levyMeasure, T.levyMeasure_condition⟩
  obtain ⟨μ, hprob, hdiv, hchar⟩ := levyKhintchine_converse V
  have hpow (ν : Measure ℝ) (n : ℕ) :
      ν.iteratedConv n = LevyFoundations.iteratedConv ν n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change ν ∗ ν.iteratedConv n = ν ∗ LevyFoundations.iteratedConv ν n
      rw [ih]
  have hexponent (ξ : ℝ) : V.exponent ξ = LevyFoundations.exponent T ξ := by
    rfl
  refine ⟨μ, hprob, ?_, ?_⟩
  · intro n hn
    obtain ⟨ν, hν, hμ⟩ := hdiv n hn
    exact ⟨ν, hν, hμ.trans (hpow ν n)⟩
  · intro ξ
    simpa only [← hexponent ξ] using hchar ξ
