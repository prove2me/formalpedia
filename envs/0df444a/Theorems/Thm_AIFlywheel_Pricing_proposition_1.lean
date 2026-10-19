-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_proposition_1
-- name    : AIFlywheel.Pricing.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:51.693785+00:00
-- url     : https://prove2.me/theorems/51a60b6a-2374-4ab0-804a-5e30cca07501
-- title:
--   Proposition 1: unique optimal contract and reduced data problem
-- statement:
--   Under the two-period model's standing assumptions, Problem (6) has a unique optimal plan. Its high-accuracy first-period data choice is the myopic quantity $\delta_{1h}=\delta^M$. Its low-accuracy choice $\delta^*$ is the unique maximizer over $[0,\nu]$ of
--   $$
--   \bar\pi_w(d_0)\left[R_\nu(\delta,\alpha_\ell)
--     +\pi_w(d_0+\delta)(\alpha_h-\alpha_\ell)\tau\right]
--     -\frac{\kappa}{\rho(d_0+\delta)}.
--   $$
--   Here $\tau=\phi^{-1}(0)\bar F(\phi^{-1}(0))$ for the standard-uniform virtual value $\phi$. This proposition links the full contract problem to the one-variable objective used in the data comparison.
--
--   **Formalization Note.** Existence and uniqueness concern the full six-variable feasible plan, while the reduced objective is used only to characterize its data choice.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 12 (PDF 13), Proposition 1; proof p. 28 (PDF 29).

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- Proposition 1, p. 12: uniqueness of the second-best contract and its data choices. -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    ∃ δstar : ℝ,
      δstar ∈ Set.Icc 0 P.ν ∧
      (∀ δ ∈ Set.Icc 0 P.ν,
        reducedMoralObjective P δ ≤ reducedMoralObjective P δstar) ∧
      (∀ δ ∈ Set.Icc 0 P.ν,
        reducedMoralObjective P δ = reducedMoralObjective P δstar →
          δ = δstar) ∧
      (∃! s : Plan, IsOptimal P s) ∧
      ∀ s : Plan, IsOptimal P s →
        s.δ1h = deltaM P.ν ∧ s.δ1l = δstar := by sorry

end AIFlywheel.Pricing
