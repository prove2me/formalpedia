-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ckOn_of_lss
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ckOn_of_lss
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:23.103953+00:00
-- url     : https://prove2.me/theorems/74f1a255-318b-4428-8f8e-601900f8d011
-- title:
--   Admissible Lie Words: ck On of lss
-- statement:
--   The Admissible Lie Words construction uses the ck On of lss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutoffIteratedFDerivBounded.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutoffIteratedFDerivBounded.lean#L16-L21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutoffIteratedFDerivBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ckOn_of_lss {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} {S : Set (Mat k r)}
    (h : LSS f S) (m : ℕ∞) : CkOn m S f := by sorry
