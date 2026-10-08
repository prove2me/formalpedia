-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_tested_vectors_decrease
-- name    : CuttingStock63.Knapsack.tested_vectors_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:12:00.978317+00:00
-- url     : https://prove2.me/theorems/136dce7a-5bb4-492a-bb4d-eaa76710148d
-- title:
--   Knapsack Method, Step (1), p. 867 — the vectors tested in Step (3) are generated in lexicographically decreasing order
-- statement:
--   Consider the Knapsack Method with lengths $l_1,\dots,l_m>0$ and stock lengths $L_1>L_2>\dots>L_k$. Let $\sigma$ be a state reachable from the start at which Step (3) is about to be executed, and let $\sigma'$ be a later state of the same run (reached by one or more steps) at which Step (3) is again about to be executed. Then the vector of $\sigma'$ is lexicographically smaller than the vector of $\sigma$, and it satisfies $L_1\ge\lambda\cdot(\alpha)_m$.
--
--   So the method generates the vectors it tests in strictly decreasing lexicographic order, among the finitely many vectors that fit the longest stock length; this is the basis of the method's termination.
--
--   **Formalization Note** The page's definition of the lexicographic order ("for some $i$, $1\le i<\min\{s_1,s_2\}$, $a_1^1=a_1^2,\dots,a_i^1=a_i^2$, while $a_{i+1}^1>a_{i+1}^2$") omits vectors that differ in their first coefficient ($i$ must range from 0); Mathlib's `Pi.Lex` order is used. The fit clause is stated for the later vector: the very first vector need not fit when $L_1<0$ (it is then the zero vector and the method stops at once).
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 867, Knapsack Method, Step (1)

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Knapsack Method, Step (1), p. 867: the vectors tested in Step (3) are generated in
lexicographically decreasing order, and every one after the first satisfies L_1 ≥ λ·(α)_m. -/
theorem tested_vectors_decrease {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hL : StrictAnti L) (σ σ' : State m k)
    (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update)
    (hσσ' : Relation.TransGen (Step l b L c) σ σ') (hu' : σ'.phase = .update) :
    toLex σ'.a < toLex σ.a ∧ Fits l (L ⟨0, hk⟩) σ'.a := by sorry

end CuttingStock63.Knapsack
