-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_Tm_dualE
-- name    : Formalism.FourierDecayAlt.P.DegreeMapArithmetic.Tm_dualE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:07.042353+00:00
-- url     : https://prove2.me/theorems/fc376b77-f7b7-4cc5-b1ad-d2d749ca0cd3
-- title:
--   Degree Map Arithmetic: Tm dual E
-- statement:
--   The Degree Map Arithmetic construction uses the Tm dual E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L65-L71

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.DegreeMapArithmetic.Tm_dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) (a b : Fin n) :
    Tm (dualE E) u a b = (Tm E u b a).dualMap := by sorry
