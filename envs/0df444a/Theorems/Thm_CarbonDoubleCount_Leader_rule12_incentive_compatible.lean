-- Prove2me | Theorems.Thm_CarbonDoubleCount_Leader_rule12_incentive_compatible
-- name    : CarbonDoubleCount.Leader.rule12_incentive_compatible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:26.051976+00:00
-- url     : https://prove2.me/theorems/3790d96f-c8bf-41e7-a20f-d6521c54e5c0
-- title:
--   Proof of Proposition 5 (A.4), p. 26 — under rule (12), e^E_n is a best response of every firm n ≠ N, i.e. (11) holds
-- statement:
--   In the model of §3 with the standing hypotheses of Proposition 5 (see the first-order identity item), let $(g^E,e^E)$ be optimal for $P_E$ with $e^E$ interior, and let $g_n$ be the linear payment rule (12). Then for every firm $n\neq N$ and every effort vector $x\in[0,A]^{m_n}$,
--   $$V_n(x)-g_n\big(f(e^E_{-n},x)\big)\;\le\;V_n(e^E_n)-g_n\big(f(e^E)\big),$$
--   where $(e^E_{-n},x)$ is the profile $e^E$ with firm $n$'s efforts replaced by $x$. That is, $e^E_n$ satisfies the incentive compatibility constraint (11) of $P_F$ when all other firms, the leader included, play $e^E$.
--
--   Together with the participation identity, this shows that rule (12) induces the effort-contracting optimum $e^E$ even though the payments see only emissions.
--
--   **Formalization Note.** $p\ge 0$ and $b_{n,i}\in\{0,1\}$ make $-p\sum_i b_{n,i}f_i$ concave in firm $n$'s effort, so firm $n$'s payoff is concave. The deviation is unilateral.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 26, proof of Proposition 5 (App. A.4), "Second, since f is concave, for the incentive compatibility constraint (11) it is sufficient to verify …"

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

namespace CarbonDoubleCount.Leader

open Finset

theorem rule12_incentive_compatible
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ) (hA : 0 < A) (hp : 0 ≤ p)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (CarbonDoubleCount.Planner.firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (CarbonDoubleCount.Planner.firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (CarbonDoubleCount.Planner.effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (CarbonDoubleCount.Planner.effortBox A))
    (hfnonneg : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ) (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ n i, (B n i = 1 ↔ ∑ j, dEff (fun e => f e i) e n j < 0))
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE)
    (hint : ∀ n j, 0 < eE n j ∧ eE n j < A) :
    ∀ n, n ≠ L → ∀ x ∈ CarbonDoubleCount.Planner.firmBox A n,
      V n x - rule12 V f p B πbar eE n (f (Function.update eE n x)) ≤
        V n (eE n) - rule12 V f p B πbar eE n (f eE) := by sorry

end CarbonDoubleCount.Leader
