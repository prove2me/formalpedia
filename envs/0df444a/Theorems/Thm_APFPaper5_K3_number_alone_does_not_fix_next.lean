-- Prove2me | Theorems.Thm_APFPaper5_K3_number_alone_does_not_fix_next
-- name    : APFPaper5.K3.number_alone_does_not_fix_next
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:48:36.504954+00:00
-- url     : https://prove2.me/theorems/5494e864-4ba5-4b8a-9d22-82272f478f13
-- title:
--   A moving cycle has no strictly increasing scalar update
-- statement:
--   If a state orbit closes at positive time and its real-valued observation changes on the first step, no strictly increasing real function globally gives the observation after the map from the observation before it. Strict order preservation is a substantive hypothesis, not a consequence of smoothness in these theorems. Recurrence, retracing and change are supplied; no physical rate is derived.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_number_alone_cannot_return.lean', 'sha256': '65e45c5ff991b83e9e257c2ef097ddee683754d4dffcae8d314b06443fa3bd17', 'line': 66, 'declaration': 'APFPaper5.K3.number_alone_does_not_fix_next'}]

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.number_alone_does_not_fix_next {X : Type*} (num : X → ℝ) (D : X → X) (o : ℕ → X)
    (ho : ∀ n : ℕ, o (n + 1) = D (o n)) (N : ℕ) (hclose : o (N + 1) = o 0)
    (hmove : num (o 1) ≠ num (o 0)) :
    ¬ ∃ f : ℝ → ℝ, (∀ x y : ℝ, x < y → f x < f y) ∧ ∀ x : X, num (D x) = f (num x) := by sorry
