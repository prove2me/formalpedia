-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_absSum_of_integral
-- name    : Formalism.ELL.FormalGroupPointsParam.absSum_of_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:25.045806+00:00
-- url     : https://prove2.me/theorems/f1b74c1b-ce60-40fc-a81e-2653ccffd84f
-- title:
--   Formal Group Points Param: abs Sum of integral
-- statement:
--   The Formal Group Points Param construction uses the abs Sum of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L95-L100

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
variable {K : Type u} [NormedField K]
variable [CompleteSpace K]

theorem Formalism.ELL.FormalGroupPointsParam.absSum_of_integral {f : PowerSeries K} (hf : IntegralPS f) {t : K} (ht : ‖t‖ < 1) :
    AbsSum f t := by sorry
