-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_mulBy_eq
-- name    : Formalism.L2.KerInert.VC.mulBy_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:38:12.091004+00:00
-- url     : https://prove2.me/theorems/5be505b1-eb5c-42bb-8208-7901442df575
-- title:
--   VC: mul By eq
-- statement:
--   The VC construction uses the mul By eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L185-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L185-L212

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
variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

theorem Formalism.L2.KerInert.VC.mulBy_eq (c : K) : Formalism.L2.Th1.C.mulBy (logSer (C • W)) (expSer (C • W)) c =
    (phi W C).subst ((Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c).subst (compInv (phi W C))) := by sorry
