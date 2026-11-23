-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wU_cc
-- name    : Formalism.L2.Th1.A.CurveSer.wU_cc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:40.603571+00:00
-- url     : https://prove2.me/theorems/408ac393-2755-4f8b-a4e3-c7a856470f12
-- title:
--   Curve Ser: w U cc
-- statement:
--   The Curve Ser construction uses the w U cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L61-L70

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_wU_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_wU_cc

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

theorem Formalism.L2.Th1.A.CurveSer.wU_cc : constantCoeff (wU W) = 1 := by sorry
