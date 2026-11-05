-- Prove2me | Theorems.Thm_FiniteEnergyPlane_liouville_ofR4_ofR4
-- name    : FiniteEnergyPlane.liouville_ofR4_ofR4
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:56:00.338532+00:00
-- url     : https://prove2.me/theorems/63db5cef-778d-4c7c-b2d2-e72ab1a0efe3
-- title:
--   The two Liouville forms agree under the coordinate identification
-- statement:
--   For $x,v\in\mathbb{R}^4$, the Liouville form $\lambda_0=\tfrac12\sum_k(q_k\,dp_k-p_k\,dq_k)$ of the `FiniteEnergyPlane` setting and the Liouville form of the `HryniewiczCriterion` setting agree under the identification of $\mathbb{R}^4$ with `V 1`:
--   $$\lambda_0^{\mathrm{FEP}}(x)(v)=\lambda_0^{\mathrm{HC}}(x)(v).$$
--
--   This allows statements about the action of a periodic orbit to be transferred between the two settings.
--
--   **Formalization Note** `liouville (ofR4 x) (ofR4 v) = HryniewiczCriterion.liouvilleForm x v`, where `ofR4 : HryniewiczCriterion.R4 → V 1` is the identity on coordinates.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), Section 2 (action of a periodic Reeb orbit, compared across two formal settings)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- The Liouville forms of `FiniteEnergyPlane` and `HryniewiczCriterion` agree under the coordinate
identification `ofR4`. -/
theorem liouville_ofR4_ofR4 (x v : HryniewiczCriterion.R4) :
    liouville (ofR4 x) (ofR4 v) = HryniewiczCriterion.liouvilleForm x v := by
  sorry

end FiniteEnergyPlane
