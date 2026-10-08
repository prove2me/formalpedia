-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_lex_predecessor
-- name    : CuttingStock63.Knapsack.lex_predecessor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:55:30.091464+00:00
-- url     : https://prove2.me/theorems/83d78972-ab9c-4889-9632-387d09229942
-- title:
--   Knapsack Method, Step (4), p. 867 — the lexicographic predecessor of (α)_m extends (α¹)_s
-- statement:
--   Let $l_1,\dots,l_m>0$ and let $(\alpha)_m$ satisfy $L\ge\lambda\cdot(\alpha)_m$. Let $s$ be the largest index with $a_s\ne0$ and let $(\alpha^1)_s$ be $(\alpha)_s$ with its $s$-th coefficient replaced by $a_s-1$. Then:
--
--   1. among the vectors $(\alpha')_m$ of nonnegative integers with $L\ge\lambda\cdot(\alpha')_m$ that are lexicographically smaller than $(\alpha)_m$ there is a lexicographically largest one;
--   2. every such lexicographically largest vector is an extension of $(\alpha^1)_s$.
--
--   This is why Step (5) starts by replacing $a_s$ by $a_s-1$: the next candidate in the lexicographic enumeration agrees with $(\alpha)_m$ before position $s$ and has $a_s-1$ in position $s$.
--
--   **Formalization Note** The page says "the lexicographically largest $m$-vector lexicographically smaller than $(\alpha)_m$"; the $m$-vectors are read as those satisfying the length constraint, as in the sentence defining the sequence of vectors (without the constraint the coordinates after $s$ are unbounded and no largest vector exists). The paper's 1-based $s$ is `i.val + 1` for the 0-based index `i`.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 867, Knapsack Method, Step (4)

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Step (4), p. 867: let (α)_m satisfy cap ≥ λ·(α)_m and let `i` (the paper's s, 0-based) be the
largest index with a_i ≠ 0. Among the m-vectors satisfying the length constraint and
lexicographically smaller than (α)_m there is a lexicographically largest one, and every such
largest vector is an extension of (α¹)_s, which differs from (α)_s only in having a_s − 1 as its
s-th coefficient. -/
theorem lex_predecessor {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (hfit : Fits l cap a) (i : Fin m) (hi : a i ≠ 0)
    (hmax : ∀ i' : Fin m, i < i' → a i' = 0) :
    (∃ g : Fin m → ℕ, Fits l cap g ∧ toLex g < toLex a ∧
        ∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g) ∧
      ∀ g : Fin m → ℕ, Fits l cap g → toLex g < toLex a →
        (∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g) →
          IsExtension (decrAt a (i.val + 1)) g (i.val + 1) := by sorry

end CuttingStock63.Knapsack
