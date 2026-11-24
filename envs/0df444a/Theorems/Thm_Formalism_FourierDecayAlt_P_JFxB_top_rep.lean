-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_top_rep
-- name    : Formalism.FourierDecayAlt.P.JFxB.top_rep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:01.931347+00:00
-- url     : https://prove2.me/theorems/e47c7f8d-7ff5-44b8-8b61-4026e359e0c9
-- title:
--   JFx B: top rep
-- statement:
--   The JFx B construction uses the top rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L138-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L138-L176

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

theorem Formalism.FourierDecayAlt.P.JFxB.top_rep {O : Set (Mat k r)} (hO : IsOpen O) {L : List (ℂ × List (Mat k r))} {j N : ℕ} (hL : WOK L j)
    (hjN : j + 1 ≤ N) (op : (Mat k r → E) → (Mat k r → E))
    (hop : ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r → op f g = wsum L f g)
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn (N : ℕ∞) (O ∩ GV k r) f)
    (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    Top (Q.EH k r) u c d (op f) g = wsum (stepL k r u c d L) f g := by sorry
