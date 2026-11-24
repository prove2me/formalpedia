-- Prove2me | Theorems.Thm_Formalism_REAL_right_derivative_sub
-- name    : Formalism.REAL.right_derivative_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:51.838832+00:00
-- url     : https://prove2.me/theorems/2e2c2bf5-f64f-4d4b-ad23-d32c3b287cee
-- title:
--   REAL: right derivative sub
-- statement:
--   The REAL construction uses the right derivative sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L141-L144

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

theorem Formalism.REAL.right_derivative_sub (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A - B) f g = Rd A f g - Rd B f g := by sorry
