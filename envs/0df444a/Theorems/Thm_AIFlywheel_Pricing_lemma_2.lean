-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_lemma_2
-- name    : AIFlywheel.Pricing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:49.186553+00:00
-- url     : https://prove2.me/theorems/b333f45b-4901-4349-8fdc-918a646394c7
-- title:
--   Lemma 2: optimal contingent payments for fixed data quantities
-- statement:
--   Fix feasible first-period data quantities $\delta_{1h},\delta_{1\ell}\in[0,\nu]$. Among all plans satisfying the limited-liability and incentive constraints of Problem (6), the unique profit-maximizing payments are
--   $$
--   x_{1\ell}=x_{2\ell}=0,\qquad
--   x_{1h}=\frac{\kappa}{\pi_w(d_0)-\pi_s(d_0)}
--     +\left(\frac{\kappa}{\rho(d_0+\delta_{1\ell})}-\kappa\right),\qquad
--   x_{2h}=\frac{\kappa}{\pi_w(d_0+\delta_{1\ell})-\pi_s(d_0+\delta_{1\ell})}.
--   $$
--   The displayed contract is feasible and uniquely maximizes the firm's full objective at those fixed data quantities. This solves the payment part of the contracting problem.
--
--   **Formalization Note.** The model's standing assumptions keep every denominator positive on the relevant data interval. The paper's final sentence on total expected payment is excluded because it conflicts with its displayed payments and equation (18).
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 26 (PDF 27), Lemma 2, first sentence; proof pp. 27–28 (PDF 28–29).

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- Lemma 2, p. 26: optimal limited-liability payments at fixed data choices. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (δ1h δ1l : ℝ)
    (hh : δ1h ∈ Set.Icc 0 P.ν) (hl : δ1l ∈ Set.Icc 0 P.ν) :
    let s0 : Plan :=
      ⟨P.κ / (P.pw P.d0 - P.ps P.d0) +
          (P.κ / dataImpact P (P.d0 + δ1l) - P.κ),
        0,
        P.κ / (P.pw (P.d0 + δ1l) - P.ps (P.d0 + δ1l)),
        0, δ1h, δ1l⟩
    s0.Feasible P ∧
      ∀ s : Plan, s.Feasible P → s.δ1h = δ1h → s.δ1l = δ1l →
        objective P s ≤ objective P s0 ∧
          (objective P s = objective P s0 → s = s0) := by sorry

end AIFlywheel.Pricing
