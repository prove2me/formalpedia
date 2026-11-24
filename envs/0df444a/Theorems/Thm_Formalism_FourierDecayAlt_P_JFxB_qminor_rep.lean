-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_qminor_rep
-- name    : Formalism.FourierDecayAlt.P.JFxB.qminor_rep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:01.14887+00:00
-- url     : https://prove2.me/theorems/dcb59395-c56a-4f47-8364-ffaeb94cbb33
-- title:
--   JFx B: qminor rep
-- statement:
--   The JFx B construction uses the qminor rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L221-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L221-L234

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

theorem Formalism.FourierDecayAlt.P.JFxB.qminor_rep {O : Set (Mat k r)} (hO : IsOpen O) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn (t : ℕ∞) (O ∩ GV k r) f) (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    qminorOp (Q.EH k r) p q u f g = wsum (qmL k r p q u) f g := by sorry
