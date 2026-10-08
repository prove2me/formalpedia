-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_tested_vector_invariant
-- name    : CuttingStock63.Knapsack.tested_vector_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:11:57.823327+00:00
-- url     : https://prove2.me/theorems/1a4e5153-409d-4a7f-aa6d-e8cd6772b5f8
-- title:
--   Knapsack Method, paragraph after Step (7), p. 868 — the invariant on entry to Step (3)
-- statement:
--   Consider the Knapsack Method with lengths $l_1,\dots,l_m>0$, prices $b_1,\dots,b_m\ge0$ ordered by density ($b_1/l_1\ge\dots\ge b_m/l_m$), stock lengths $L_1>\dots>L_k$ and costs $c_1,\dots,c_k$. Let $\sigma$ be a reachable state at which Step (3) is about to test the vector $(\alpha)_m$, with current values $M_1,\dots,M_k$. Then:
--
--   1. for every $j$, $c_j\le M_j$, and either $M_j=c_j$ or $M_j=\beta\cdot(\alpha')_m$ for some vector with $L_j\ge\lambda\cdot(\alpha')_m$;
--   2. every vector $(\alpha')_m$ with $L_1\ge\lambda\cdot(\alpha')_m$ that is lexicographically larger than $(\alpha)_m$ satisfies
--   $$
--   \beta\cdot(\alpha')_m\le M_1 .
--   $$
--
--   Clause 2 says that, for the longest stock length, every vector above the one being tested has already been accounted for; it is the invariant behind the paper's justification "each succeeding vector tested in (3) is the lexicographically next largest $m$-vector that can satisfy $L_t\ge\lambda\cdot(\alpha)_m$ and $\beta\cdot(\alpha)_m>M_j$".
--
--   **Formalization Note** Clause 2 is stated for $L_1$ only, because for the shorter stock lengths it is false: with $m=1$, $l_1=b_1=1$, $L=(5,2)$, $c=(0,0)$, the method tests $(5)$, then the test of Step (5) at $(4)$ fails for $j=2$ only because $4>L_2$, Step (6) stops, and the vectors $(2),(1)$, which fit $L_2$, are never examined. With a single stock length ($k=1$) the statement is the paper's claim in full. Nonnegative prices are a disclosed hypothesis (see the goal theorem).
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 868, Knapsack Method, paragraph after Step (7)

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Knapsack Method, paragraph after Step (7), p. 868, in corrected form: on every entry to
Step (3) of every run, (i) for every j, c_j ≤ M_j and M_j is c_j or the objective of a vector
satisfying L_j ≥ λ·(α)_m; and (ii) for the longest stock length L_1, every vector satisfying
L_1 ≥ λ·(α)_m that is lexicographically larger than the vector about to be tested has objective
at most M_1. (Clause (ii) fails for the shorter stock lengths: see the Formalization Note.) -/
theorem tested_vector_invariant {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L)
    (σ : State m k) (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update) :
    (∀ j : Fin k, c j ≤ σ.M j ∧
        (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
      ∀ a' : Fin m → ℕ, toLex σ.a < toLex a' → Fits l (L ⟨0, hk⟩) a' →
        bet b a' m ≤ σ.M ⟨0, hk⟩ := by sorry

end CuttingStock63.Knapsack
