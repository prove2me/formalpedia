-- Prove2me | Theorems.Thm_Formalism_REAL_vector_right_derivative_neg
-- name    : Formalism.REAL.vector_right_derivative_neg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:57:12.920827+00:00
-- url     : https://prove2.me/theorems/8f17b525-e136-4334-a290-6e748c5111f2
-- title:
--   REAL: vector right derivative neg
-- statement:
--   The REAL construction uses the vector right derivative neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L145-L149

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.REAL.vector_right_derivative_neg (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hB : inG ε B) (hg : inUJ ε g) :
    RdV (-B) f g = -RdV B f g := by sorry
