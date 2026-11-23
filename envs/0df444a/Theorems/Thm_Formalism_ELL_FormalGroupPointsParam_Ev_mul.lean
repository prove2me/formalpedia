-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
-- name    : Formalism.ELL.FormalGroupPointsParam.Ev.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:08.615531+00:00
-- url     : https://prove2.me/theorems/478d7c0f-ada3-44cc-ab9e-533f357a57da
-- title:
--   Ev: mul
-- statement:
--   The Ev construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L61-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L61-L83

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

theorem Formalism.ELL.FormalGroupPointsParam.Ev.mul {f g : PowerSeries K} {t a b : K} (hf : Ev f t a) (hg : Ev g t b) :
    Ev (f * g) t (a * b) := by sorry
