-- Prove2me | Theorems.Thm_APFPaper5_K3_closing_orbit_does_not_move
-- name    : APFPaper5.K3.closing_orbit_does_not_move
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:30:09.656944+00:00
-- url     : https://prove2.me/theorems/498b35e3-6a0f-448b-80c8-9805a5e60475
-- title:
--   Closing orbit does not move
-- statement:
--   A sequence iterating a strictly increasing real function that returns to its initial value at positive time has its first two values equal. Strict order preservation is a substantive hypothesis, not a consequence of smoothness in these theorems. Recurrence, retracing and change are supplied; no physical rate is derived.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_number_alone_cannot_return.lean', 'sha256': '65e45c5ff991b83e9e257c2ef097ddee683754d4dffcae8d314b06443fa3bd17', 'line': 54, 'declaration': 'APFPaper5.K3.closing_orbit_does_not_move'}]

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.closing_orbit_does_not_move (f : ℝ → ℝ) (hf : ∀ x y : ℝ, x < y → f x < f y)
    (u : ℕ → ℝ) (hu : ∀ n : ℕ, u (n + 1) = f (u n)) (N : ℕ) (hN : u (N + 1) = u 0) :
    u 1 = u 0 := by sorry
