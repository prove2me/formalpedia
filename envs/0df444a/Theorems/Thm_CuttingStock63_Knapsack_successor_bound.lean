-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_successor_bound
-- name    : CuttingStock63.Knapsack.successor_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:01:25.815896+00:00
-- url     : https://prove2.me/theorems/f0691bad-c959-4bd0-99fa-20bdaa187ffb
-- title:
--   Knapsack Method, p. 868 — after a failed test in Step (5), no vector before the successor of Step (6) improves M_j
-- statement:
--   Let $l_1,\dots,l_m>0$ and $b_1,\dots,b_m\ge0$ be ordered by density, $b_1/l_1\ge\dots\ge b_m/l_m$, with the slack item $b_{m+1}=0$, $l_{m+1}=1$. Let $1\le s\le m$, let $(\alpha)_s$ be a prefix, and let $L$, $M$ be a stock length and its current maximum such that the inequality of the test of Step (5) fails:
--   $$
--   (L-\lambda\cdot(\alpha)_s)\,b_{s+1}\;\le\;(M-\beta\cdot(\alpha)_s)\,l_{s+1}.
--   $$
--   Then every vector $(\alpha')_m$ of nonnegative integers with $a'_i=a_i$ for $i\le s-1$, $a'_s\le a_s$ and $L\ge\lambda\cdot(\alpha')_m$ satisfies $\beta\cdot(\alpha')_m\le M$.
--
--   These are exactly the vectors lexicographically between $(\alpha)_s$ and the successor computed in Step (6), the lexicographically largest $(s-1)$-vector smaller than $(\alpha)_s$; so after a failed test the method may jump to that successor without missing an improvement of $M$.
--
--   **Formalization Note** This is the corrected form of the page's claim. The page concludes from "the failure of the necessary condition in (5)" for every $j$; but the test of Step (5) for $j$ also requires $L_j\ge\lambda\cdot(\alpha)_s$, and when that part fails for a shorter stock length, smaller values of $a_s$ may still fit $L_j$ and improve $M_j$. The statement therefore assumes the failure of the inequality itself (which is what the test establishes for every $j$ whose length accommodates the prefix). Nonnegative prices are a disclosed hypothesis, as for the relaxation bound.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 868, Knapsack Method, paragraph before Step (5) (successor calculated in (6))

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Knapsack Method, paragraph before Step (5), p. 868 (the successor of Step (6)), in corrected
form: if the inequality of the test of Step (5) fails for a stock length L with current value M at
the prefix (α)_s, that is (L − λ·(α)_s) b_{s+1} ≤ (M − β·(α)_s) l_{s+1}, then no vector a' that
agrees with (α)_s in its first s − 1 coefficients, has a'_s ≤ a_s and satisfies L ≥ λ·(α')_m
improves M. Hence nothing between (α)_s and the successor computed in Step (6) can improve M. -/
theorem successor_bound {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (L M : ℝ) (a : Fin m → ℕ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsm : s ≤ m)
    (hfail : (L - lam l a s) * nextB b s ≤ (M - bet b a s) * nextL l s)
    (a' : Fin m → ℕ) (hpre : ∀ i : Fin m, i.val + 1 < s → a' i = a i)
    (hlast : ∀ i : Fin m, i.val + 1 = s → a' i ≤ a i) (hfit : Fits l L a') :
    bet b a' m ≤ M := by sorry

end CuttingStock63.Knapsack
