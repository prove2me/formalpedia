-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_om_mul_D
-- name    : Formalism.L2.Th1.A.CurveSer.om_mul_D
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:08.41401+00:00
-- url     : https://prove2.me/theorems/e3463d15-61a7-478e-828b-cb2fad991660
-- title:
--   Curve Ser: om mul D
-- statement:
--   The Curve Ser construction uses the om mul D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L138-L139

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

theorem Formalism.L2.Th1.A.CurveSer.om_mul_D (f : R⟦X⟧) : om W * D W f = derivative R f := by sorry
