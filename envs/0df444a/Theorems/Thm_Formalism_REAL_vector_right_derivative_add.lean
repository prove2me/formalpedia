-- Prove2me | Theorems.Thm_Formalism_REAL_vector_right_derivative_add
-- name    : Formalism.REAL.vector_right_derivative_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:05.050723+00:00
-- url     : https://prove2.me/theorems/3841c5e4-b812-4db7-ab8f-73892c7a22c9
-- title:
--   REAL: vector right derivative add
-- statement:
--   The REAL construction uses the vector right derivative add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L151-L153

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

theorem Formalism.REAL.vector_right_derivative_add (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnGV ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : RdV (A + B) f g = RdV A f g + RdV B f g := by sorry
