-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_hasDeriv
-- name    : Formalism.FourierDecayAlt.P.JFxB.wsum_hasDeriv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:11.069516+00:00
-- url     : https://prove2.me/theorems/5f7bbe38-3129-4f5f-ac09-3d1fe1bb12e6
-- title:
--   JFx B: wsum has Deriv
-- statement:
--   The JFx B construction uses the wsum has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L65-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L65-L99

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

theorem Formalism.FourierDecayAlt.P.JFxB.wsum_hasDeriv {O : Set (Mat k r)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j)
    {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => wsum L f (crv (false, X) g t)) (wsum (L.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by sorry
