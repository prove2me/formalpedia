-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_eval_le
-- name    : Formalism.ELL.FormalGroupPointsParam.norm_eval_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:49.142517+00:00
-- url     : https://prove2.me/theorems/e2fee07f-7aa4-479e-9eca-a483dec3c25a
-- title:
--   Formal Group Points Param: norm eval le
-- statement:
--   The Formal Group Points Param construction uses the norm eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L133-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L133-L144

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

theorem Formalism.ELL.FormalGroupPointsParam.norm_eval_le [CompleteSpace K] {f : PowerSeries K} (hf : IntegralPS f) (h0 : coeff 0 f = 0)
    {t : K} (ht : ‖t‖ < 1) : ‖evalPS f t‖ ≤ ‖t‖ := by sorry
