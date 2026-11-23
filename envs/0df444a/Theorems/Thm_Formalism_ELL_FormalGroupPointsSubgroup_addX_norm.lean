-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_addX_norm
-- name    : Formalism.ELL.FormalGroupPointsSubgroup.addX_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:53.687076+00:00
-- url     : https://prove2.me/theorems/f63643f3-72fc-4f35-85d4-7399e66ae830
-- title:
--   Formal Group Points Subgroup: add X norm
-- statement:
--   The Formal Group Points Subgroup construction uses the add X norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L87-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L87-L171

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.FormalGroupPointsSubgroup.addX_norm [DecidableEq K] (W : WeierstrassCurve K) (hW : IntegralModel W)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) (hx₁ : 1 < ‖x₁‖) (hx₂ : 1 < ‖x₂‖) :
    1 < ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ := by sorry
