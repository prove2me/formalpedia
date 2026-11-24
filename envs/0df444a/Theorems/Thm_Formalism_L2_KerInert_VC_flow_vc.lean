-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_flow_vc
-- name    : Formalism.L2.KerInert.VC.flow_vc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:19.046552+00:00
-- url     : https://prove2.me/theorems/28a7c44d-3e68-4c5d-a740-a67858e554b5
-- title:
--   VC: flow vc
-- statement:
--   The VC construction uses the flow vc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L21-L25

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

theorem Formalism.L2.KerInert.VC.flow_vc (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    U*(((1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) - r*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2))*v + (u - r*w)*(-v^2*(s*(1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) + (t - s*r)*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2)))) =
      U*(1 - (Ui*(a1+2*s))*(U*(u - r*w)*v) - (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2 - 2*(Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v) - 2*(Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v) - 3*(Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^2) := by sorry
