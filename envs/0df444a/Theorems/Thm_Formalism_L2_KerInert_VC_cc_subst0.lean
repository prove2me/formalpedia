-- Prove2me | Theorems.Thm_Formalism_L2_KerInert_VC_cc_subst0
-- name    : Formalism.L2.KerInert.VC.cc_subst0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:03.907408+00:00
-- url     : https://prove2.me/theorems/c101934f-b837-46e4-ba48-4ae0ab342417
-- title:
--   VC: cc subst0
-- statement:
--   The VC construction uses the cc subst0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/VarChange.lean#L131-L133

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
variable {R : Type} [CommRing R]

theorem Formalism.L2.KerInert.VC.cc_subst0 {f a : R⟦X⟧} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 := by sorry
