-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_identical_prices
-- name    : CuttingStock63.Knapsack.identical_prices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:07:23.939335+00:00
-- url     : https://prove2.me/theorems/b9e420ee-2efc-4afb-baf8-1d077a89b565
-- title:
--   Identical Prices, p. 869, paragraph ‘Clearly, identical prices …’ — among lengths with identical prices only the shortest is needed
-- statement:
--   Let $l_1,\dots,l_m$ be lengths and $b_1,\dots,b_m$ prices, and let $i\ne j$ be two items with $l_i<l_j$ and $b_i=b_j$. Then for every vector $(\alpha)_m$ of nonnegative integers with $L\ge\lambda\cdot(\alpha)_m$ there is a vector $(\alpha')_m$ with
--   $$
--   L\ge\lambda\cdot(\alpha')_m,\qquad a'_j=0,\qquad \beta\cdot(\alpha')_m=\beta\cdot(\alpha)_m .
--   $$
--   (Substitute the shorter length $l_i$ for every piece of length $l_j$.) Hence the maximum of the knapsack problem (1) is unchanged when the variable $a_j$ is dropped, and among lengths with identical prices only the shortest needs to be considered.
--
--   **Formalization Note** The page's remark that "the density $b_i/l_i$ associated with $l_i$ is greater" holds only for $b_i>0$; it is an aside and not part of the claim, which needs neither positive lengths nor the density order.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 869, Identical Prices, paragraph beginning ‘Clearly, identical prices’

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Identical Prices, paragraph "Clearly, identical prices …", p. 869: if l_i < l_j and b_i = b_j, then every vector
satisfying the constraint of (1) can be replaced by one with a_j = 0, still satisfying the
constraint, with the same objective (substitute l_i for every piece of length l_j). So the
maximum of (1) does not change when the variable a_j is dropped. -/
theorem identical_prices {m : ℕ} (l b : Fin m → ℝ) (L : ℝ) (i j : Fin m) (hij : i ≠ j)
    (hlt : l i < l j) (hbeq : b i = b j) (a : Fin m → ℕ) (ha : Fits l L a) :
    ∃ a' : Fin m → ℕ, Fits l L a' ∧ a' j = 0 ∧ bet b a' m = bet b a m := by sorry

end CuttingStock63.Knapsack
