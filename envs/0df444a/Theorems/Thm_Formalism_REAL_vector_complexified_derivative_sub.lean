-- Prove2me | Theorems.Thm_Formalism_REAL_vector_complexified_derivative_sub
-- name    : Formalism.REAL.vector_complexified_derivative_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:58:05.671798+00:00
-- url     : https://prove2.me/theorems/3dc099cf-63ae-4375-a48d-7e22149a423a
-- title:
--   REAL: vector complexified derivative sub
-- statement:
--   The REAL construction uses the vector complexified derivative sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L199-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L199-L211

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

theorem Formalism.REAL.vector_complexified_derivative_sub (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnGV ε f) (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Z - W) f g = EcV ε Z f g - EcV ε W f g := by sorry
