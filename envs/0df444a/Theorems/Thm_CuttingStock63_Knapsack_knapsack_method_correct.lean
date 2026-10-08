-- Prove2me | Theorems.Thm_CuttingStock63_Knapsack_knapsack_method_correct
-- name    : CuttingStock63.Knapsack.knapsack_method_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:12:14.302892+00:00
-- url     : https://prove2.me/theorems/69a97314-98ee-4e55-95c0-dd634aaf044b
-- title:
--   Knapsack Method, pp. 867–868 — every run terminates, never gets stuck, and ends with M_1 = max(c_1, the knapsack optimum for L_1)
-- statement:
--   Consider the Knapsack Method of Gilmore and Gomory (Steps (2)–(7)) with $m\ge1$ demanded lengths $l_1,\dots,l_m>0$, prices $b_1,\dots,b_m\ge0$, and $k\ge1$ stock lengths $L_1,\dots,L_k$ with costs $c_1,\dots,c_k$, where the data are sorted as in Step (1):
--   $$
--   \frac{b_1}{l_1}\ge\frac{b_2}{l_2}\ge\dots\ge\frac{b_m}{l_m},\qquad L_1>L_2>\dots>L_k .
--   $$
--   Then:
--
--   1. **Termination.** Every run from the start of Step (2) is finite: no reachable state begins an infinite sequence of steps.
--   2. **Progress.** Every reachable state at which the method has not stopped has a next step.
--   3. **Correctness.** At every reachable state at which the method has stopped, for every $j$, $c_j\le M_j$ and $M_j$ is either $c_j$ or the price $\sum_i b_ia_i$ of a column with $\sum_i l_ia_i\le L_j$; and for the longest stock length
--   $$
--   M_1=\max\Big(c_1,\ \max\Big\{\sum_{i=1}^m b_ia_i : a_i\in\mathbb Z_{\ge0},\ \sum_{i=1}^m l_ia_i\le L_1\Big\}\Big).
--   $$
--   With a single stock length ($k=1$) this is the paper's claim, "the final values of the maxima $M_j$ are the desired maxima when the algorithm terminates in Step (6)", in full: the method solves the knapsack problem (1).
--
--   **Formalization Note** The page claims $M_j=\max(c_j,\bar M_j)$ for *every* $j$. That is false as the steps are printed when $k\ge2$: with $m=1$, $l_1=b_1=1$, $L=(5,2)$, $c=(0,0)$, the method tests $(5)$ (so $M_1=5$), the test of Step (5) at $(4)$ holds for no $j$ ($j=1$ fails the inequality, $j=2$ fails $L_2\ge4$), Step (6) stops, and the run ends with $M_2=0$ although the column $(2)$ has price 2. (A sorry-free Lean proof of this run accompanies the mission.) The statement keeps the printed algorithm and claims exactly what holds for it. Disclosed hypotheses: $l_i>0$ (demanded lengths) and $b_i\ge0$; with a negative price the method is wrong (for $m=2$, $b=(-1,-2)$, $l=(1,1)$, $L=2$, $c=-5$ it ends with $M=-2$ although the zero vector gives $0$), and the paper applies it to cutting-stock prices, which are nonnegative. Step (1) is stated as hypotheses on the input rather than as a sorting step. Termination is part of the statement so that the correctness clause is not vacuous; the algorithm's output is never defined as the knapsack maximum, and the maximum is the predicate `IsKnapsackMax`, not a real `sSup` (which is 0 on an empty set).
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), pp. 866–868, definition of M_j and Knapsack Method, Steps (1)–(7) and the paragraph after Step (7)

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method

namespace CuttingStock63.Knapsack

/-- Knapsack Method, Steps (1)–(7) and the paragraph after Step (7), p. 868, in corrected form:
for data sorted as in Step (1), every run of the method from Step (2) is finite, a state other
than the end always has a next step, and at the end every M_j is c_j or attained by a vector
satisfying L_j ≥ λ·(α)_m with c_j ≤ M_j, while M_1 (the longest stock length) is exactly
max(c_1, M̄_1). With one stock length (k = 1) this is the paper's claim in full. -/
theorem knapsack_method_correct {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (l b : Fin m → ℝ)
    (L c : Fin k → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L) :
    (∀ σ : State m k, Reachable l b L c hk σ → Acc (fun x y => Step l b L c y x) σ) ∧
      (∀ σ : State m k, Reachable l b L c hk σ → σ.phase ≠ .done →
        ∃ σ' : State m k, Step l b L c σ σ') ∧
      (∀ σ : State m k, Reachable l b L c hk σ → σ.phase = .done →
        (∀ j : Fin k, c j ≤ σ.M j ∧
            (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
          IsKnapsackMax l b (L ⟨0, hk⟩) (c ⟨0, hk⟩) (σ.M ⟨0, hk⟩)) := by sorry

end CuttingStock63.Knapsack
