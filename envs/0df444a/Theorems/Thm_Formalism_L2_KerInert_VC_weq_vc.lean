-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_weq_vc
-- name    : Formalism.L2.KerInert.VC.weq_vc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:25.343798+00:00
-- url     : https://prove2.me/theorems/5aee6b7a-5ea1-43f4-ba65-c3d0ee8267b3
-- title:
--   VC: weq vc
-- statement:
--   The VC construction uses the weq vc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L16-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_InertKernelTheory_InertCoprimeLemmas_VarChange
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv

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
variable {A : Type*} [CommRing A] (a1 a2 a3 a4 a6 U Ui r s t u w v : A)

theorem Formalism.L2.KerInert.VC.weq_vc (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    (U^3*w*v) = (U*(u - r*w)*v)^3 + (Ui*(a1+2*s))*(U*(u - r*w)*v)*(U^3*w*v) + (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2*(U^3*w*v) + (Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v)^2 + (Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v)^2 + (Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^3 := by sorry
