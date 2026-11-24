-- Prove2me | Theorems.Thm_Formalism_REAL_complexified_derivative_commutator
-- name    : Formalism.REAL.complexified_derivative_commutator
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:39.097787+00:00
-- url     : https://prove2.me/theorems/9e47dec8-8a1c-4660-9202-a66e3c5319bb
-- title:
--   REAL: complexified derivative commutator
-- statement:
--   The REAL construction uses the complexified derivative commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L160-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L160-L183

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.complexified_derivative_commutator (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) {n : ℕ}
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Ec ε Z (Ec ε W f) g - Ec ε W (Ec ε Z f) g = Ec ε (Z * W - W * Z) f g := by sorry
