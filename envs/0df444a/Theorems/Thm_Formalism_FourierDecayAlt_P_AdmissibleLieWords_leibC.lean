-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_leibC
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.leibC
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:48.201915+00:00
-- url     : https://prove2.me/theorems/df8c518a-c25b-4e45-a1a2-c9b8ecefaaea
-- title:
--   Admissible Lie Words: leib C
-- statement:
--   The Admissible Lie Words construction uses the leib C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L143-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleWordLengthLe.lean#L143-L154

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
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
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.leibC (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) (a : Mat k r → (F →L[ℂ] E)) (b : Mat k r → F)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hM : ∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) :
    ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by sorry
