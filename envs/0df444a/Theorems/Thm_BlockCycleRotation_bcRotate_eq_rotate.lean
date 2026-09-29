-- Prove2me | Theorems.Thm_BlockCycleRotation_bcRotate_eq_rotate
-- name    : BlockCycleRotation.bcRotate_eq_rotate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:03.688375+00:00
-- url     : https://prove2.me/theorems/1b7db116-1180-4a79-bfd5-15a2ee0c8e69
-- title:
--   Correctness of the block cycle algorithm
-- statement:
--   Let $l$ be a list and $k \le |l|$. Writing $\operatorname{bcRotate}$ for the block cycle procedure of §2 implemented on lists,
--   $$\operatorname{bcRotate}(l,k) = \operatorname{rotate}(l,k),$$
--   where $\operatorname{rotate}$ is Mathlib's list rotation. The procedure recurses by exchanging blocks while $2k \le |l|$, and reduces the remaining case $k > |l|/2$ by reversing the list and rotating by $|l|-k$.
--
--   **What this does and does not establish.** It establishes that the procedure computes the rotation — a cost bound on an algorithm that computed something else would be worthless, and the paper describes the scheme without proving this. It does **not** connect $\operatorname{bcRotate}$ to the cost recursion the rest of the development analyses.
--
--   That connection is the paper's **equation (1)**. The paper introduces $\mathrm{Cost}(n,k,b)$ as *the number of moves the method needs*, and then states equation (1) — the three-branch recursion — as holding for $k \le n/2$. This formalization takes that recursion as the *definition* of the cost, so equation (1) is assumed rather than proved. Establishing it would mean modelling the in-place algorithm as a sequence of element moves and showing that count satisfies the recursion; it remains open here.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §2. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Rotate.lean#L97-L135

import Definitions.Def_BlockCycleRotation_Rotate
import Mathlib

open BlockCycleRotation
variable {α : Type*}

theorem BlockCycleRotation.bcRotate_eq_rotate : ∀ (l : List α) (k : ℕ), k ≤ l.length →
    bcRotate l k = l.rotate k := by sorry
