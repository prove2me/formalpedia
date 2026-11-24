-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_ckOn_Rw_loc
-- name    : Formalism.FourierDecayAlt.P.JFxB.ckOn_Rw_loc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:26:01.161599+00:00
-- url     : https://prove2.me/theorems/cfe7f823-fe62-4cb7-824b-9d8fc38877ca
-- title:
--   JFx B: ck On Rw loc
-- statement:
--   The JFx B construction uses the ck On Rw loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L51-L63

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

theorem Formalism.FourierDecayAlt.P.JFxB.ckOn_Rw_loc {UU : Set (Mat k r)} {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) {j : ℕ}
    (hj : w.length + 1 ≤ j + 1) {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) UU f) :
    CkOn 1 UU (Rw w f) := by sorry
