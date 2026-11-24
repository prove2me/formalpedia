-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ck_lsum
-- name    : Formalism.FourierDecayAlt.P.JFxE.ck_lsum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:38.523798+00:00
-- url     : https://prove2.me/theorems/7c78ab33-f574-4c89-abaa-ee15c3b5b79c
-- title:
--   JFx E: ck lsum
-- statement:
--   The JFx E construction uses the ck lsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L205-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L205-L221

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem Formalism.FourierDecayAlt.P.JFxE.ck_lsum {m : ℕ∞} (L : List (ℂ × (Mat k r → E))) (h : ∀ p ∈ L, CkOn m (GV k r) p.2) :
    CkOn m (GV k r) (fun x => (L.map fun p => p.1 • p.2 x).sum) := by sorry
