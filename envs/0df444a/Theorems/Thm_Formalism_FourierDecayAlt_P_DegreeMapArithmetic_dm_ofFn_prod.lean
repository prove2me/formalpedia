-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_ofFn_prod
-- name    : Formalism.FourierDecayAlt.P.DegreeMapArithmetic.dm_ofFn_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:13:10.123148+00:00
-- url     : https://prove2.me/theorems/5b20de7e-46fd-440a-a177-6ad61a598a1c
-- title:
--   Degree Map Arithmetic: dm of Fn prod
-- statement:
--   The Degree Map Arithmetic construction uses the dm of Fn prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L51-L57

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

theorem Formalism.FourierDecayAlt.P.DegreeMapArithmetic.dm_ofFn_prod : ∀ {t : ℕ} (f : Fin t → Module.End ℂ V),
    ((List.ofFn f).prod).dualMap = (List.ofFn fun i => (f i.rev).dualMap).prod
  := by sorry
