-- Prove2me | Theorems.Thm_BlockCycleRotation_sqrt_le_cutoff
-- name    : BlockCycleRotation.sqrt_le_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:55.171648+00:00
-- url     : https://prove2.me/theorems/88c1dae2-e926-4149-b19a-cd24ea247934
-- title:
--   `√m ≤ 4√d·N`
-- statement:
--   **`√m ≤ 4√d·N`**, the real form of `cutoff_lower`.
--
--   In Blomer–Bux this is **Lemma 19**, “Cut-off lower bound `m ≤ 16d·N²`”. It is used in the proof of `Eterm_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L632-L649

import Mathlib

open Real Finset

theorem BlockCycleRotation.sqrt_le_cutoff {m d : ℕ} (hd : 0 < d) (h : 2 * d ≤ m) :
    Real.sqrt (m : ℝ)
      ≤ 4 * Real.sqrt (d : ℝ) * ((Nat.sqrt (m / (2 * d)) : ℕ) : ℝ) := by sorry
