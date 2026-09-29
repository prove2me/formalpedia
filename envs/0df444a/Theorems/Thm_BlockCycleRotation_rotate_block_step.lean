-- Prove2me | Theorems.Thm_BlockCycleRotation_rotate_block_step
-- name    : BlockCycleRotation.rotate_block_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:45.507792+00:00
-- url     : https://prove2.me/theorems/18436ccf-a475-417b-90dd-ec13ae561203
-- title:
--   The block cycle step
-- statement:
--   **The block cycle step.** With `m = ⌊n / k⌋ * k` the length of the part covered by whole blocks, splitting `l = P ++ Q` with `P = l.take m` and `Q = l.drop m`: * `P.drop k` (the first `(b-1) * k` entries) is already in final position, and * the remaining suffix is `(P.take k ++ Q).rotate k`, a rotation of a list of length `k + n % k` — the subproblem the algorithm recurses on.
--
--   In Blomer–Bux this is **§2, Fig. 1**, “Block cycle step is correct”. It is used in the proof of `bcRotate_eq_rotate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §2, Fig. 1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Rotate.lean#L19-L60

import Mathlib

variable {α : Type*}

theorem BlockCycleRotation.rotate_block_step (l : List α) {k : ℕ} (hk : 0 < k) (hkn : k ≤ l.length) :
    l.rotate k =
      (l.take (l.length / k * k)).drop k ++
        ((l.take (l.length / k * k)).take k ++ l.drop (l.length / k * k)).rotate k := by sorry
