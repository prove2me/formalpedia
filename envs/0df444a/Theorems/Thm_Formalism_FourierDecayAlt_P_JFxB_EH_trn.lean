-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_trn
-- name    : Formalism.FourierDecayAlt.P.JFxB.EH_trn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:08:44.724549+00:00
-- url     : https://prove2.me/theorems/8484fd7e-e8f1-4bb1-b769-fd14cd659e1b
-- title:
--   JFx B: EH trn
-- statement:
--   The JFx B construction uses the EH trn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L203-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L203-L211

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem Formalism.FourierDecayAlt.P.JFxB.EH_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, Q.EH k r c d (trn L a b f) g = trn L a b (EHc k r b c d f) g := by sorry
