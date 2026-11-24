-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_weight_mono
-- name    : Formalism.FourierDecayAlt.P.DegreeMapArithmetic.weight_mono
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:45.742035+00:00
-- url     : https://prove2.me/theorems/32a3d547-2386-450e-beef-4cc5bf1e221f
-- title:
--   Degree Map Arithmetic: weight mono
-- statement:
--   The Degree Map Arithmetic construction uses the weight mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L119-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean#L119-L139

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

theorem Formalism.FourierDecayAlt.P.DegreeMapArithmetic.weight_mono {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hE : GlRel E) (c : Fin n) (m : ℂ)
    (w : V) (hw : E c.castSucc c.castSucc w = m • w) (a : Fin n → ℕ) :
    E c.castSucc c.castSucc (mono (etaK E) a w) = (m + (a c : ℂ)) • mono (etaK E) a w := by sorry
