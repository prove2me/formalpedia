-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_8
-- name    : BudgetFeasSubmod.Main.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:16.965983+00:00
-- url     : https://prove2.me/theorems/610c0520-55b0-49bd-974d-293bb8c7bd36
-- title:
--   Lemma 3.8, p. 12 — if opt(A,B) > k·max v(i), Sample-then-Greedy is a constant-factor approximation with probability ≥ 1/2
-- statement:
--   Let $A$ be a nonempty finite set of agents, $v$ a normalized non-negative submodular valuation, $B>0$, $c\in[0,B]^A$, and $\beta>0$ the parameter of Simultaneous Greedy. Let $\mathrm{alg}_1$ be a deterministic e-approximation for the knapsack-constrained problem, $\mathrm{alg}_2$ a 2-approximation for unconstrained maximization, and fix a cost-independent arg-max tie-breaking rule. If for some positive integer $k$
--   $$
--   \mathrm{opt}(A,B)>k\cdot\max_{i\in A}v(i),
--   $$
--   then, with $\ell=\lfloor\frac{k-1}{4e\beta}\rfloor$, with probability at least $1/2$ over the random halving $A_1$, Sample-then-Greedy$(A,v,c,B)$, run with parameter $\beta$, outputs a set $S$ with
--   $$
--   v(S)\ge\min\Big\{\frac{\ell\,(k-1)}{e(\ell+1)},\ \frac{\beta(k-1)-8k}{6}\Big\}\cdot\frac{1}{4\beta k}\cdot\mathrm{opt}(A,B).
--   $$
--
--   This is the approximation guarantee of the sampling branch of GenSm-Main when no single agent carries a large share of the optimum.
--
--   **Formalization Note** The probability is a count over the $2^{|A|}$ subsets $A_1$: $2^{|A|}\le 2\cdot\#\{\text{good }A_1\}$. $\mathrm{alg}_1$ is deterministic with $\mathrm{opt}(X,B)\le e\cdot v(\mathrm{alg}_1(X))$, the simplification the paper itself makes (footnote 3, Remark 3.10); it also returns a budget-feasible subset of its input, which the proof uses for $\mathrm{opt}(A,B)\ge x$. $\lfloor\cdot\rfloor$ is `Nat.floor`; when it is $0$ the bound is non-positive. $e$ is `Real.exp 1`. The lemma is stated for every $\beta>0$, as the paper's analysis is independent of $\beta$ (p. 8); GenSm-Main and Corollary 3.9 use $\beta=9.185$.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 12, Lemma 3.8 (footnote 3)

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

open Finset

/-- Lemma 3.8, p. 12: if `opt(A, B) > k · max_{i ∈ A} v(i)` for a positive integer `k`, then with
probability at least `1/2` (a count over the `2^n` halvings `A₁`) Sample-then-Greedy (with any parameter `β > 0`) outputs `S`
with `v(S) ≥ min{⌊(k−1)/(4eβ)⌋(k−1)/(e(⌊(k−1)/(4eβ)⌋+1)), (β(k−1)−8k)/6} · opt(A, B)/(4βk)`. -/
theorem lemma_3_8 {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (v : Finset A → ℝ)
    (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B : ℝ) (c : A → ℝ) (k : ℕ)
    (hv : IsValuation v) (h1 : IsKnapsackEApprox v B alg1) (h2 : IsUnconstrainedTwoApprox v alg2)
    (htb : IsArgmaxRule v tb) (hβ : 0 < β) (hB : 0 < B) (hc : InDomain B c) (hk : 0 < k)
    (hopt : ∀ i : A, (k : ℝ) * v {i} < opt v c B univ) :
    2 ^ Fintype.card A ≤ 2 * (univ.powerset.filter (fun A₁ : Finset A =>
      min ((⌊((k : ℝ) - 1) / (4 * Real.exp 1 * β)⌋₊ : ℝ) * ((k : ℝ) - 1) /
            (Real.exp 1 * ((⌊((k : ℝ) - 1) / (4 * Real.exp 1 * β)⌋₊ : ℝ) + 1)))
          ((β * ((k : ℝ) - 1) - 8 * k) / 6) * (1 / (4 * β * k)) * opt v c B univ ≤
        v (sampleThenGreedy v alg1 alg2 tb β B A₁ c))).card := by sorry

end BudgetFeasSubmod.Main
