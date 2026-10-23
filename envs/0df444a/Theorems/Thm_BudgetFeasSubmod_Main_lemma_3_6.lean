-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_6
-- name    : BudgetFeasSubmod.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:57.053227+00:00
-- url     : https://prove2.me/theorems/58d23fb7-d797-4306-a88b-ae27bba9e1b7
-- title:
--   Lemma 3.6, p. 10 — if max v(i) < x/(ℓβ), Simultaneous Greedy's output has v(S) ≥ min{ℓx/((ℓ+1)β), (opt(D,B) − 2x/β)/6}
-- statement:
--   Let $v$ be a normalized non-negative submodular valuation on a finite agent set $A$, $B>0$, $\beta>0$, $D\subseteq A$, and let $c\in[0,B]^A$ be the costs. Fix a cost-independent arg-max tie-breaking rule and a 2-approximation $\mathrm{alg}_2$ for unconstrained maximization. If $\ell$ is a positive integer with $v(i)<\frac{x}{\ell\beta}$ for every $i\in D$, then the set $S$ returned by Simultaneous Greedy$(D,v,c,B,x)$ satisfies
--   $$
--   v(S)\ge\min\Big\{\frac{\ell x}{(\ell+1)\beta},\ \frac16\Big(\mathrm{opt}(D,B)-\frac{2x}{\beta}\Big)\Big\}.
--   $$
--
--   This is the approximation guarantee of Simultaneous Greedy for a fixed rate $x$; it is useful when $x$ is a constant-factor estimate of the optimum and no single agent is too valuable, which is what the sampling in Sample-then-Greedy arranges.
--
--   **Formalization Note** $\beta$ is a parameter, any $\beta>0$ (p. 8: the analysis is independent of its value). "$\max_{i\in D}v(i)<x/(\ell\beta)$" is stated agent by agent. Costs lie in $[0,B]$ (Remark 2.5).
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 10, Lemma 3.6

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

/-- Lemma 3.6, p. 10: if `max_{i ∈ D} v(i) < x/(ℓβ)` for a positive integer `ℓ`, the output `S` of
Simultaneous Greedy(D, v, c, B, x) has `v(S) ≥ min{ℓx/((ℓ+1)β), (opt(D, B) − 2x/β)/6}`. -/
theorem lemma_3_6 {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ)
    (alg2 : Finset A → Finset A) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (D : Finset A) (c : A → ℝ) (ℓ : ℕ)
    (hv : IsValuation v) (h2 : IsUnconstrainedTwoApprox v alg2) (htb : IsArgmaxRule v tb)
    (hβ : 0 < β) (hB : 0 < B) (hc : InDomain B c) (hℓ : 0 < ℓ)
    (hmax : ∀ i ∈ D, v {i} < x / ((ℓ : ℝ) * β)) :
    min ((ℓ : ℝ) * x / (((ℓ : ℝ) + 1) * β)) ((opt v c B D - 2 * x / β) / 6) ≤
      v (simGreedy v alg2 tb β B x D c) := by sorry

end BudgetFeasSubmod.Main
