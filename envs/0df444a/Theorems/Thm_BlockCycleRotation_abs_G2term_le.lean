-- Prove2me | Theorems.Thm_BlockCycleRotation_abs_G2term_le
-- name    : BlockCycleRotation.abs_G2term_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:51.975185+00:00
-- url     : https://prove2.me/theorems/6d30033a-5a9e-4368-b74f-4b8bd3c46f4c
-- title:
--   Lemma 16 at a single coprime pair
-- statement:
--   For a bulk pair $a > a' \ge 1$ with $d\,a(a+a') \le m$,
--   $$|G_2(m,d,a,a')| \le |A(m,d,a)| + |B(a,a')|\, Y(m,a,a'),$$
--   where $A$ and $B$ are the constant and linear coefficients of the inner sum and $Y$ its cut-off. The per-pair form of Lemma 16; summing it over pairs and divisors gives the global bound.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 16. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L224-L290

import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.abs_G2term_le {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hbulk : d * a * (a + a') ≤ m) :
    |G2term m d a a'| ≤ |aCoeff m d a| + |bCoeff a a'| * yCut m a a' := by sorry
