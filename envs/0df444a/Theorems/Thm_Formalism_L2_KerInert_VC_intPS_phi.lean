-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_intPS_phi
-- name    : Formalism.L2.KerInert.VC.intPS_phi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:36.076062+00:00
-- url     : https://prove2.me/theorems/043b9344-db57-40a3-8df3-8c2601617a6a
-- title:
--   VC: int PS phi
-- statement:
--   The VC construction uses the int PS phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L266-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L266-L274

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
open Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] (R' : Subring K)
variable {R'}

theorem Formalism.L2.KerInert.VC.intPS_phi (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R') : IntPS R' (phi W C) := by sorry
