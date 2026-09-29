-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma17_final
-- name    : BlockCycleRotation.lemma17_final
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:17.26729+00:00
-- url     : https://prove2.me/theorems/3cd82389-12a8-4615-9eab-38d77d4f9894
-- title:
--   Lemma 19 with the error term instantiated
-- statement:
--   For $n>0$,
--   $$\left| G_1(n) - C\,n^2\sum_{d\mid n}\frac{1}{d^2} \right| \le \sum_{d\mid n} \mathrm{Eterm}(n,d),$$
--   with $\mathrm{Eterm}$ the explicit per-divisor error supplied by the local form of Lemma 19.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L599-L603

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.lemma17_final {n : ℕ} (hn : 0 < n) :
    |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ n.divisors, Eterm n d := by sorry
