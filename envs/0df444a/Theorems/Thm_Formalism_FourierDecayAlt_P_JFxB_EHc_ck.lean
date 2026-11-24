-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_ck
-- name    : Formalism.FourierDecayAlt.P.JFxB.EHc_ck
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:51.392798+00:00
-- url     : https://prove2.me/theorems/2c4dc9e2-a4fd-4a9c-b423-d54cc684e73e
-- title:
--   JFx B: EHc ck
-- statement:
--   The JFx B construction uses the EHc ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L196-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L196-L201

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

theorem Formalism.FourierDecayAlt.P.JFxB.EHc_ck {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (EHc k r y c d f) := by sorry
