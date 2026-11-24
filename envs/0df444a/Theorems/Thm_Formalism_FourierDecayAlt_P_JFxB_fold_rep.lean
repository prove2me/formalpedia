-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_fold_rep
-- name    : Formalism.FourierDecayAlt.P.JFxB.fold_rep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:05.2077+00:00
-- url     : https://prove2.me/theorems/21554021-4e5e-42da-9f85-b1e7bfaeff23
-- title:
--   JFx B: fold rep
-- statement:
--   The JFx B construction uses the fold rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L191-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L191-L204

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxB.fold_rep {O : Set (Mat k r)} (hO : IsOpen O) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ {N : ℕ}, ts.length ≤ N → ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r →
      (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g = wsum (foldL k r ts) f g := by sorry
