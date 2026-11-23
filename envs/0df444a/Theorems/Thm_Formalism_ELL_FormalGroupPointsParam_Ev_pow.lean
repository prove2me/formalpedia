-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
-- name    : Formalism.ELL.FormalGroupPointsParam.Ev.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:38.66116+00:00
-- url     : https://prove2.me/theorems/63bbee8d-20ac-4077-a79b-f6577632262f
-- title:
--   Ev: pow
-- statement:
--   The Ev construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L85-L93

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

theorem Formalism.ELL.FormalGroupPointsParam.Ev.pow {f : PowerSeries K} {t a : K} (hf : Ev f t a) (n : ℕ) : Ev (f ^ n) t (a ^ n) := by sorry
