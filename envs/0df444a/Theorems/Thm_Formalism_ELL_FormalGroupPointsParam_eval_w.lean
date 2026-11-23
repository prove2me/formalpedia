-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_eval_w
-- name    : Formalism.ELL.FormalGroupPointsParam.eval_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:30.762021+00:00
-- url     : https://prove2.me/theorems/5bb513ab-fd43-48c0-be1f-c8001e1d3861
-- title:
--   Formal Group Points Param: eval w
-- statement:
--   The Formal Group Points Param construction uses the eval w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L168-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L168-L193

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]

theorem Formalism.ELL.FormalGroupPointsParam.eval_w {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) {t : K} (ht : ‖t‖ < 1) :
    evalPS w t = t ^ 3 + W.a₁ * t * evalPS w t + W.a₂ * t ^ 2 * evalPS w t
        + W.a₃ * evalPS w t ^ 2 + W.a₄ * t * evalPS w t ^ 2 + W.a₆ * evalPS w t ^ 3 ∧
      ‖evalPS w t‖ = ‖t‖ ^ 3 := by sorry
