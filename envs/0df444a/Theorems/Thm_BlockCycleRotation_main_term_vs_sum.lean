-- Prove2me | Theorems.Thm_BlockCycleRotation_main_term_vs_sum
-- name    : BlockCycleRotation.main_term_vs_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:28.180527+00:00
-- url     : https://prove2.me/theorems/56311af5-4883-4bc4-9d75-5fdf4f5a6b9e
-- title:
--   The rounding term, in the paper's form
-- statement:
--   **The rounding term, in the paper's form.** The paper compares the closed form at the *real* bound `V` — namely `A·V + B·V²/2` — with the actual sum `∑_{1 ≤ b' < V} (A + B·b')`, and bounds the difference by `|A| + |B·V|`. Writing `K` for the largest admissible `b'`, so that `K ≤ V < K+1` and the sum is `A·K + B·K(K+1)/2`, that is what is proved here.
--
--   In Blomer–Bux this is **Lemma 19 / §4**, “Rounding term (paper's `G₂` form)”. It is used in the proofs of `abs_G2term_le`, `bulk_pair_estimate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19 / §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1495-L1524

import Mathlib

open Real Finset

theorem BlockCycleRotation.main_term_vs_sum (A B V : ℝ) (K : ℕ) (hK : (K : ℝ) ≤ V) (hK1 : V ≤ (K : ℝ) + 1)
    (hV : 1 ≤ V) :
    |(A * V + B * V ^ 2 / 2) - (A * (K : ℝ) + B * ((K : ℝ) * ((K : ℝ) + 1)) / 2)|
      ≤ |A| + |B| * V := by sorry
