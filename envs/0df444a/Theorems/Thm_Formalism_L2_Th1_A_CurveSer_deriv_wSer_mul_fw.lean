-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_deriv_wSer_mul_fw
-- name    : Formalism.L2.Th1.A.CurveSer.deriv_wSer_mul_fw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:33.855065+00:00
-- url     : https://prove2.me/theorems/20a8de5b-6ddb-4530-94a6-78ff2b120c09
-- title:
--   Curve Ser: deriv w Ser mul fw
-- statement:
--   The Curve Ser construction uses the deriv w Ser mul fw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L131-L136

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem Formalism.L2.Th1.A.CurveSer.deriv_wSer_mul_fw : derivative R (wSer W) * fw W = fu W := by sorry
