-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_intPS_compInv
-- name    : Formalism.L2.KerInert.VC.intPS_compInv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:41.013102+00:00
-- url     : https://prove2.me/theorems/46c9d6c8-65a4-4bda-80ed-f1b44f393ea5
-- title:
--   VC: int PS comp Inv
-- statement:
--   The VC construction uses the int PS comp Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L249-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L249-L262

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

theorem Formalism.L2.KerInert.VC.intPS_compInv {f : K⟦X⟧} (hf : IntPS R' f) (h0 : constantCoeff f = 0) {u ui : K} (hui : ui ∈ R')
    (h1 : coeff 1 f = u) (huu : u * ui = 1) : IntPS R' (compInv f) := by sorry
