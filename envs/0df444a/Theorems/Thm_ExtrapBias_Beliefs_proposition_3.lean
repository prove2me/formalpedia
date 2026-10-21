-- Prove2me | Theorems.Thm_ExtrapBias_Beliefs_proposition_3
-- name    : ExtrapBias.Beliefs.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:56.446571+00:00
-- url     : https://prove2.me/theorems/4909ad40-31ed-4130-9dc0-6b3c971ab26d
-- title:
--   Proposition 3 (19), p. 16, corrected — unique investment and worst-case angle
-- statement:
--   At a state with positive firm size δ, let Vδ and VM be positive marginal values of size and cash. For the HJB bracket (18), the unique maximizing investment i* and, for each investment, the unique minimizing worst-case angle φ* on [0,2π] satisfy
--   $$
--   V_M(1+\theta i^*)=V_\delta,\qquad
--   \phi^*=\arctan\!\left(\frac{V_M}{V_\delta}\frac{\sigma_Y\kappa_T}{\sigma_\delta\kappa_P}\right)\in(0,\pi/2).
--   $$
--   These first-order conditions allocate the manager’s pessimism between permanent and temporary shocks.
--
--   **Formalization Note** The printed investment equation (19) has an extra δ on its left side. Differentiating the bracket (18) yields the corrected equation displayed here. Positivity of δ, Vδ and VM gives the unique optimizer and a meaningful arctangent ratio.
-- source:
--   Lee & Rivera, Extrapolation Bias and Dynamic Liquidity Management, working paper (May 24, 2019), p. 16, Proposition 3 (19); p. 15, (18)

import Mathlib
import Definitions.Def_ExtrapBias_Beliefs_Model

namespace ExtrapBias.Beliefs

/-- Proposition 3 (19), p. 16, corrected: the printed investment FOC
has a spurious factor δ on its left side. -/
theorem proposition_3 (p : Params) (δ M Vd VM Vdd VMM : ℝ)
    (hδ : 0 < δ) (hVd : 0 < Vd) (hVM : 0 < VM) :
    let iStar := (Vd - VM) / (p.theta * VM)
    let phiStar := Real.arctan ((VM / Vd) *
      (p.sigY * p.kapT / (p.sigD * p.kapP)))
    VM * (1 + p.theta * iStar) = Vd ∧
    phiStar ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
    (∀ φ : ℝ, ∀ i : ℝ,
      bracket18 p Vd VM Vdd VMM δ M i φ ≤
        bracket18 p Vd VM Vdd VMM δ M iStar φ ∧
      (bracket18 p Vd VM Vdd VMM δ M i φ =
        bracket18 p Vd VM Vdd VMM δ M iStar φ → i = iStar)) ∧
    (∀ i : ℝ, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      bracket18 p Vd VM Vdd VMM δ M i phiStar ≤
        bracket18 p Vd VM Vdd VMM δ M i φ ∧
      (bracket18 p Vd VM Vdd VMM δ M i φ =
        bracket18 p Vd VM Vdd VMM δ M i phiStar → φ = phiStar)) := by sorry

end ExtrapBias.Beliefs
