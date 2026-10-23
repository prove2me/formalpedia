-- Prove2me | Theorems.Thm_BitranCaldentey2003_prop8_eq35_convex_region_faithful
-- name    : BitranCaldentey2003.prop8_eq35_convex_region_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:03:59.52199+00:00
-- url     : https://prove2.me/theorems/d8f98b8e-55fa-460f-9864-db3e313ad1ae
-- title:
--   Proposition 8, eq. (35), with concave objective and convex feasible region (as stated)
-- statement:
--   Consider the $N$-period pricing model ($N\ge 1$) with initial inventory $C_0$: in period $n$ a price $p_n\ge 0$ is charged and the demand $D_n(p_n)\ge 0$ is random, independent across periods. Let $V_1(C_0)$ be the optimal expected revenue of the dynamic program, and let $p^{\det}$ be an optimal solution of the deterministic problem
--
--   $$V_1^{\det}(C_0)=\max_{p\ge 0}\sum_{n=1}^N p_nE[D_n(p_n)]\quad\text{s.t.}\quad\sum_{n=1}^N E[D_n(p_n)]\le C_0.$$
--
--   Assume that the objective is concave on $[0,\infty)^N$, that the feasible region $\{p\ge 0:\sum_n E[D_n(p_n)]\le C_0\}$ is convex, that some price $p^\infty\ge 0$ has $\sum_n E[D_n(p^\infty)]<C_0$, and that each $D_n(p_n^{\det})$ has finite variance and positive mean, with $V_1^{\det}(C_0)>0$. Let $V_1(p^{\det},C_0)$ be the expected revenue of charging $p_n^{\det}$ in period $n$, $\mathscr D_n^{\det}=\sum_{i\le n}D_i(p_i^{\det})$, $\sigma_n^2=\operatorname{Var}(\mathscr D_n^{\det})$ and $\eta_n^{\det}(C_0)=\tfrac12\big(\sqrt{\sigma_n^2+(C_0-E[\mathscr D_n^{\det}])^2}-(C_0-E[\mathscr D_n^{\det}])\big)$. Then
--
--   $$1\ge\frac{V_1(p^{\det},C_0)}{V_1(C_0)}\ge\frac{1}{V_1^{\det}(C_0)}\sum_{n=1}^N p_n^{\det}E[D_n(p_n^{\det})]\Big(1-\frac{\eta_n^{\det}(C_0)}{E[D_n(p_n^{\det})]}\Big)\ge1-\max_n\frac{\eta_n^{\det}(C_0)}{E[D_n(p_n^{\det})]}.$$
--
--   This is eq. (35) of Proposition 8 of Bitran and Caldentey (2003), under the hypotheses the proposition states: a concave objective and a convex feasible region. The existing theorem PricingRM.DetHeuristic.det_price_heuristic_ratio_bound assumes instead that every mean-demand function $p\mapsto E[D_n(p)]$ is convex on $[0,\infty)$, which implies a convex feasible region but is not implied by it.
--
--   **Formalization Note** Concavity of the separable objective on $[0,\infty)^N$ is equivalent to concavity of each $p\mapsto pE[D_n(p)]$ on $[0,\infty)$. The finite-variance and positivity conditions are made explicit because the paper takes variances and divides by these quantities. $V_1(C_0)$ is the Bellman value computed in $[0,\infty]$ and converted to a real number.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, Manufacturing & Service Operations Management 5(3):203–229 (2003), doi:10.1287/msom.5.3.203.16061, p. 221, Proposition 8, eq. (35) (definitions (32)–(34)); proof in the Appendix, pp. 226–227

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic
open scoped ENNReal

theorem BitranCaldentey2003.prop8_eq35_convex_region_faithful {N : ℕ} (M : PricingModel N)
    (hN : 0 < N)
    (hconc : ConcaveOn ℝ (Set.univ.pi fun _ : Fin N => Set.Ici (0 : ℝ)) (detObjective M))
    (C₀ : ℝ) (hconvF : Convex ℝ {q : Fin N → ℝ | DetFeasible M C₀ q})
    (hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand M n pinf < C₀)
    (pdet : Fin N → ℝ) (hopt : IsDetOptimal M C₀ pdet)
    (hL2 : ∀ n, MemLp (fun x : ℝ => x) 2 (M.μ n (pdet n)))
    (hmean : ∀ n, 0 < meanDemand M n (pdet n))
    (hVdet : 0 < detObjective M pdet) :
    1 ≥ heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ∧
      heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ≥
        (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ∧
      (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ≥
        1 - Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun n => eta M C₀ pdet n / meanDemand M n (pdet n)) := by sorry
