-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_comm_prod
-- name    : Formalism.FourierDecayAlt.P.DegreeMapArithmetic.comm_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:13:14.267249+00:00
-- url     : https://prove2.me/theorems/6bb667e4-1706-44ee-9fe8-44263c0e911f
-- title:
--   Degree Map Arithmetic: comm prod
-- statement:
--   The Degree Map Arithmetic construction uses the comm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L94-L102

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

theorem Formalism.FourierDecayAlt.P.DegreeMapArithmetic.comm_prod (H : Module.End ℂ V) : ∀ {n : ℕ} (g : Fin n → Module.End ℂ V) (e : Fin n → ℂ),
    (∀ x, H * g x = g x * H + e x • g x) →
    H * (List.ofFn g).prod = (List.ofFn g).prod * H + (∑ x, e x) • (List.ofFn g).prod
  := by sorry
