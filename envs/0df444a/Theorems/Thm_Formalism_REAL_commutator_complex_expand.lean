-- Prove2me | Theorems.Thm_Formalism_REAL_commutator_complex_expand
-- name    : Formalism.REAL.commutator_complex_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:52.222799+00:00
-- url     : https://prove2.me/theorems/8644e944-8f84-44de-8341-fe1cb07c6be0
-- title:
--   REAL: commutator complex expand
-- statement:
--   The REAL construction uses the commutator complex expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ComplexifiedDerivativeCommutator.lean#L121-L126

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

theorem Formalism.REAL.commutator_complex_expand {n : ℕ} (X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ) :
    (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
      ((X1 * Y1 - Y1 * X1) - (X2 * Y2 - Y2 * X2)) +
        Complex.I • ((X1 * Y2 - Y2 * X1) + (X2 * Y1 - Y1 * X2)) := by sorry
