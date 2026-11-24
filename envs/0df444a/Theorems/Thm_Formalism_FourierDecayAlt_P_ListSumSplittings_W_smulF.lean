-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_W_smulF
-- name    : Formalism.FourierDecayAlt.P.ListSumSplittings.W_smulF
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:10:20.811165+00:00
-- url     : https://prove2.me/theorems/45000ec2-1ed2-4509-ba12-7975d50e2cfb
-- title:
--   List Sum Splittings: W smul F
-- statement:
--   The List Sum Splittings construction uses the W smul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L93-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListSumSplittings.lean#L93-L118

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.ListSumSplittings.W_smulF : ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ (f : Mat k r → ℂ) (H : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) H → ∀ g ∈ GV k r,
      W w (fun g => f g • H g) g = ((splits w).map fun p => W p.1 f g • W p.2 H g).sum := by sorry
