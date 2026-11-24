-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_arg_rev
-- name    : Formalism.FourierDecayAlt.P.DegreeMapArithmetic.arg_rev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:28:25.264251+00:00
-- url     : https://prove2.me/theorems/2f57b980-5a7a-49b2-ba27-b737f61e22c4
-- title:
--   Degree Map Arithmetic: arg rev
-- statement:
--   The Degree Map Arithmetic construction uses the arg rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L73-L78

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_arg_rev

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

theorem Formalism.FourierDecayAlt.P.DegreeMapArithmetic.arg_rev {t : ℕ} (w : ℂ) (j : Fin t) :
    w - (t : ℂ) + 1 + (((Fin.rev j : Fin t) : ℕ) : ℂ) = w - ((j : ℕ) : ℂ) := by sorry
