-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_greedy_lex_largest
-- name    : CuttingStock63.Knapsack.greedy_lex_largest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:11:49.641484+00:00
-- url     : https://prove2.me/theorems/b7b89eb2-6b9f-4eb6-9d68-b646bdb3a817
-- title:
--   Knapsack Method, Steps (2) and (7), pp. 867–868 — the greedy completion is the lexicographically largest feasible extension
-- statement:
--   Let $l_1,\dots,l_m>0$, let $L$ be a capacity, and let $(\alpha)_s$ be a prefix ($0\le s\le m$) with $\lambda\cdot(\alpha)_s\le L$. Let $(\gamma)_m$ be the greedy completion of Steps (2) and (7): $\gamma_i=a_i$ for $i\le s$ and
--   $$
--   \gamma_i=\Big[\frac{L-(\lambda\cdot(\alpha)_s+l_{s+1}\gamma_{s+1}+\dots+l_{i-1}\gamma_{i-1})}{l_i}\Big],\qquad i=s+1,\dots,m.
--   $$
--   Then $(\gamma)_m$ is an extension of $(\alpha)_s$, it satisfies $L\ge\lambda\cdot(\gamma)_m$, and every extension $(\alpha')_m$ of $(\alpha)_s$ with $L\ge\lambda\cdot(\alpha')_m$ is lexicographically at most $(\gamma)_m$.
--
--   With $s=0$ this is the first claim of Step (2): the first vector of the method is the lexicographically largest $m$-vector satisfying $L_1\ge\lambda\cdot(\alpha)_m$. With $s\ge1$ it is the claim behind Step (7).
--
--   **Formalization Note** The page writes "which satisfies $L_t\ge\lambda\cdot(\alpha)_s$" in Step (7); the prefix already satisfies that, and the intended condition is on the extension, $L_t\ge\lambda\cdot(\alpha)_m$, which is what is stated. The lexicographic order is Mathlib's `Pi.Lex` (`toLex`). Positive lengths are the paper's standing setting (demanded lengths).
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), pp. 867–868, Knapsack Method, Step (2) and the paragraph before Step (5) (Step (7))

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Steps (2) and (7), pp. 867–868: if the prefix (α)_s satisfies cap ≥ λ·(α)_s, the greedy
completion of Steps (2)/(7) is the lexicographically largest extension (α)_m of (α)_s that
satisfies cap ≥ λ·(α)_m. With `s = 0` this is Step (2)'s "lexicographically largest m-vector". -/
theorem greedy_lex_largest {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (s : ℕ) (hs : s ≤ m) (hfit : lam l a s ≤ cap) :
    IsExtension a (greedyFill l cap a s) s ∧ Fits l cap (greedyFill l cap a s) ∧
      ∀ a' : Fin m → ℕ, IsExtension a a' s → Fits l cap a' →
        toLex a' ≤ toLex (greedyFill l cap a s) := by sorry

end CuttingStock63.Knapsack
