-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_relaxation_bound
-- name    : CuttingStock63.Knapsack.relaxation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:57:22.241534+00:00
-- url     : https://prove2.me/theorems/d410a4e4-8fa2-4b17-8e10-9094fb90f4cb
-- title:
--   Knapsack Method, paragraph before Step (5), p. 867 — the LP-relaxation bound β·(α)_s + b_{s+1}(L − λ·(α)_s)/l_{s+1}
-- statement:
--   Let $l_1,\dots,l_m>0$ and $b_1,\dots,b_m\ge0$ be ordered by density, $b_1/l_1\ge b_2/l_2\ge\dots\ge b_m/l_m$, and append the slack item $a_{m+1}$ with $b_{m+1}=0$, $l_{m+1}=1$. Let $1\le s\le m$ and let $(\alpha)_s$ be a prefix. Then every extension $(\alpha')_m$ of $(\alpha)_s$ with $L\ge\lambda\cdot(\alpha')_m$ satisfies
--   $$
--   \beta\cdot(\alpha')_m\;\le\;\beta\cdot(\alpha)_s+\frac{b_{s+1}\,(L-\lambda\cdot(\alpha)_s)}{l_{s+1}}.
--   $$
--   Equivalently, $\beta\cdot(\alpha)_s+b_{s+1}(L_j-\lambda\cdot(\alpha)_s)/l_{s+1}>M_j$ is a necessary condition for some extension of $(\alpha)_s$ to improve the current maximum $M_j$: the value obtained by relaxing the integrality of $a_{s+1}$ and setting $a_{s+1}=(L_j-\lambda\cdot(\alpha)_s)/l_{s+1}$.
--
--   This bound is the test of Step (5), which lets the method skip every extension of a prefix that cannot improve any $M_j$.
--
--   **Formalization Note** Nonnegative prices are a disclosed hypothesis: Step (1) places the slack item, of density 0, after every item, which presupposes $b_i/l_i\ge0$, and the paper applies the method to cutting-stock prices, which are nonnegative. At $s=m$ the right side is $\beta\cdot(\alpha)_m$ and the claim is immediate.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 867, Knapsack Method, paragraph before Step (5)

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-- Knapsack Method, paragraph before Step (5), p. 867: with the variables ordered by density
b_1/l_1 ≥ ⋯ ≥ b_m/l_m (and the slack item a_{m+1}, b_{m+1} = 0, l_{m+1} = 1, last), every
extension (α)_m of (α)_s with L ≥ λ·(α)_m has β·(α)_m ≤ β·(α)_s + b_{s+1}(L − λ·(α)_s)/l_{s+1}.
So β·(α)_s + b_{s+1}(L_j − λ·(α)_s)/l_{s+1} > M_j is necessary for an extension to improve M_j. -/
theorem relaxation_bound {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (L : ℝ) (a : Fin m → ℕ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsm : s ≤ m) (a' : Fin m → ℕ) (hext : IsExtension a a' s)
    (hfit : Fits l L a') :
    bet b a' m ≤ bet b a s + nextB b s * (L - lam l a s) / nextL l s := by sorry

end CuttingStock63.Knapsack
