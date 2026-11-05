-- Prove2me | Theorems.Thm_FiniteEnergyPlane_integral_liouvilleForm_eq
-- name    : FiniteEnergyPlane.integral_liouvilleForm_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:58:41.185651+00:00
-- url     : https://prove2.me/theorems/b9109444-67de-49a8-b1c1-e3f74cbd62e4
-- title:
--   The action of a periodic orbit agrees in the two Liouville conventions
-- statement:
--   Let $R=(x,T)$ be a periodic orbit of $H_0$ on $\mathbb{R}^4$ in the `HryniewiczCriterion` setting. Then its action computed with the Liouville form of that setting equals the action of the curve $x$, viewed in `V 1`, computed with the Liouville form of the `FiniteEnergyPlane` setting:
--   $$\int_0^T\lambda_0^{\mathrm{HC}}(x(t))(\dot x(t))\,dt=\int_0^T\lambda_0^{\mathrm{FEP}}(x(t))(\dot x(t))\,dt.$$
--
--   This lets a bound on the action stated in one setting be used in the other, for example when comparing periods of Reeb orbits with hypotheses on actions.
--
--   **Formalization Note** The right-hand integrand is `liouville (ofR4 (R.x τ)) (deriv (fun s => ofR4 (R.x s)) τ)`, with `ofR4 : HryniewiczCriterion.R4 → V 1` the identity on coordinates. No hypothesis on $H_0$ is needed.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), Section 2 (action of a periodic Reeb orbit, compared across two formal settings)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- The action of a periodic orbit `R` of `HryniewiczCriterion` is the same whether computed with
`HryniewiczCriterion.liouvilleForm` or, after the identification `ofR4`, with the Liouville form of
`FiniteEnergyPlane`. -/
theorem integral_liouvilleForm_eq (H₀ : HryniewiczCriterion.R4 → ℝ)
    (R : HryniewiczCriterion.PeriodicOrbit H₀) :
    (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) =
      ∫ τ in (0 : ℝ)..R.T, liouville (ofR4 (R.x τ)) (deriv (fun s => ofR4 (R.x s)) τ) := by
  sorry

end FiniteEnergyPlane
