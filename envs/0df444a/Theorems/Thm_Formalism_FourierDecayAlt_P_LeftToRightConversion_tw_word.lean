-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_tw_word
-- name    : Formalism.FourierDecayAlt.P.LeftToRightConversion.tw_word
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:25:56.575154+00:00
-- url     : https://prove2.me/theorems/3ae53603-c4fa-4d32-8f3b-1096f4545fda
-- title:
--   Left To Right Conversion: tw word
-- statement:
--   The Left To Right Conversion construction uses the tw word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L147-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftToRightConversion.lean#L147-L208

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.LeftToRightConversion.tw_word {A c : ℝ} {m : ℕ} {F : Mat k r → E} (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F)
    (hR : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ GV k r, gN g ^ A * ‖Rw v F g‖ ≤ c)
    (u v : List (Mat k r)) (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, unitLie k r X)
    (hl : u.length + v.length ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GV k r, gN g ^ (A - 2 * (m : ℝ)) * ‖dLR u v F g‖ ≤ C := by sorry
