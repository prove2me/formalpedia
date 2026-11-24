-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_weq_phi
-- name    : Formalism.L2.KerInert.VC.weq_phi
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:36:50.327359+00:00
-- url     : https://prove2.me/theorems/b81f556e-8bae-4332-b6c3-ff3d6c6b7f2b
-- title:
--   VC: weq phi
-- statement:
--   The VC construction uses the weq phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L71-L81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.KerInert Formalism.L2.KerInert.VC
open Formalism.L2.Th1.A
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)

theorem Formalism.L2.KerInert.VC.weq_phi : psi W C = phi W C ^ 3 + PowerSeries.C (C • W).a₁ * phi W C * psi W C
    + PowerSeries.C (C • W).a₂ * phi W C ^ 2 * psi W C + PowerSeries.C (C • W).a₃ * psi W C ^ 2
    + PowerSeries.C (C • W).a₄ * phi W C * psi W C ^ 2 + PowerSeries.C (C • W).a₆ * psi W C ^ 3 := by sorry
