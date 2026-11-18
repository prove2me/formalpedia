-- Prove2me | Theorems.Thm_EditGV897_Main_affine_counter_program
-- name    : EditGV897.Main.affine_counter_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:37:05.907951+00:00
-- url     : https://prove2.me/theorems/cd0ffbf4-37c4-4ec3-aaa1-62616a040045
-- title:
--   Finite tape program for exact affine-system counts
-- statement:
--   There is a fixed finite binary tape program that counts the solutions of any binary affine equation system. For a system of $m$ equations in $n$ binary variables, its input gives the dimension and the dense coefficient rows with their right-hand sides. Its output is the canonical binary representation of the specified Gaussian-elimination count, including zero for inconsistent systems.
--
--   For uniform natural constants $A>0$ and $d$, the program has an actual halting execution of at most
--
--   $$A(n+m+1)^d$$
--
--   transitions. The bound includes parsing, elimination, binary arithmetic and output writing. This is the exact affine-counting subroutine used in the source's conditional-expectation construction.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 Gaussian elimination and §4.1 Lemma 1, printed pp.8–10 / PDF pp.9–11

import Definitions.Def_EditGV897_Main_Construction
open EditGV897.Main

theorem EditGV897.Main.affine_counter_program : ∃ (counter : Program) (A d : ℕ), 0 < A ∧
    ∀ (n : ℕ) (E : List (Equation n)),
      Runs counter (unary n ++ equationCode E) (binary (affineCount E))
        (polyBudget A d (n + E.length)) := by sorry
