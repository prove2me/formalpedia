-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_proposition_2
-- name    : AIFlywheel.Pricing.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:53.664999+00:00
-- url     : https://prove2.me/theorems/59783562-23b8-44de-8fbe-61d577760e6f
-- title:
--   Proposition 2: unique first-best data choice
-- statement:
--   The first-best problem, which fixes all four payments at the effort cost $\kappa$ and removes the incentive constraints, has a unique optimal pair of data quantities. The high-accuracy choice is $\delta_{1h}=\delta^M$. The low-accuracy choice $\delta^{FB}$ uniquely maximizes over $[0,\nu]$
--   $$
--   R_\nu(\delta,\alpha_\ell)
--     +\pi_w(d_0+\delta)(\alpha_h-\alpha_\ell)\tau,
--   \qquad \delta^{FB}>\delta^M.
--   $$
--   This establishes the benchmark against which the contract's data choice is compared.
--
--   **Formalization Note.** The full first-best objective is maximized globally over both data choices; the displayed one-variable problem characterizes its low-accuracy component.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 13 (PDF 14), Proposition 2; proof pp. 28–29 (PDF 29–30).

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- Proposition 2, p. 13: the unique first-best choice exceeds the myopic quantity. -/
theorem proposition_2 (P : Params) (hP : P.Standing) :
    ∃ δFB : ℝ,
      δFB ∈ Set.Icc 0 P.ν ∧
      (∀ δ ∈ Set.Icc 0 P.ν,
        reducedFBObjective P δ ≤ reducedFBObjective P δFB) ∧
      (∀ δ ∈ Set.Icc 0 P.ν,
        reducedFBObjective P δ = reducedFBObjective P δFB → δ = δFB) ∧
      deltaM P.ν < δFB ∧
      (∃! p : ℝ × ℝ, IsFBOptimal P p.1 p.2) ∧
      ∀ h l : ℝ, IsFBOptimal P h l →
        h = deltaM P.ν ∧ l = δFB := by sorry

end AIFlywheel.Pricing
