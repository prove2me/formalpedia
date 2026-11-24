-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_Supplement_allocation_regret_counterexample
-- name    : BayesProphet.MultiSec.Supplement.allocation_regret_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:12:21.992568+00:00
-- url     : https://prove2.me/theorems/afd7e5c6-a800-49f5-a721-052ba79d4161
-- title:
--   Theorem 5 (refuted; corrected to its negation) — the Online Allocation regret bound of the Fluid Bayes Selector fails
-- statement:
--   Theorem 5 of the paper (p. 26) claims the following. Consider Online Allocation with $d$ resources, $n$ types and, for each type $j$, a collection $S_j$ of $m_j$ distinct multiset bundles with multiplicities $a_{is}\in\mathbb N$, and fix a norm $\mu$ on $\mathbb R^n$. Then there is a constant $\kappa>0$, depending only on the bundle collections (and $\mu$), such that for all nonnegative bundle rewards $r_{sj}$, every horizon $T$ and every arrival law satisfying Eq. (17), i.e. for every $j$ there are $c_j\ge0$ and $\tau_j\in\mathbb N$ with
--   $$\mathbb P\Big[\|Z(t)-\mathbb E Z(t)\|_\mu\ \ge\ \frac{\mathbb E[Z_j(t)]}{\kappa(|S_j|+1)}\Big]\ \le\ \frac{c_j}{t^2}\qquad\forall t\in[T],\ t>\tau_j,$$
--   and for every $p_j\ge\mathbb P[\theta^t=j]$ ($t\in[T]$), every initial budget $B\in\mathbb N^d$, every selection of optimal solutions $X^t$ of the fluid LPs (16) and every tie-breaking rule, the Fluid Bayes Selector (Algorithm 4) satisfies
--   $$\mathbb E[\mathrm{Reg}]\ \le\ r_{\max}\sum_{j\in[n]}p_j\,(c_j+\tau_j).$$
--
--   **This claim is false**, and the statement here is its negation. A counterexample: one type ($n=1$), one resource ($d=1$) with initial budget $B=3$, horizon $T=2$, and two bundles: $s_a$ uses $2$ units and has reward $3$, $s_b$ uses $1$ unit and has reward $1$. The arrivals are deterministic, so $Z(t)=\mathbb E Z(t)=t$. The event in Eq. (17) then never occurs for any $\kappa>0$, so $c_1=0$ and $\tau_1=0$ are admissible, and with $p_1=1$ the claimed bound is $0$. At $t=2$, the unique optimum of (16) is $x_{s_a}=3/2$, $x_{s_b}=0$, $x_{\text{fict}}=1/2$, so Algorithm 4 assigns $s_a$ and earns $3$. At $t=1$ the remaining budget is $1$, and the unique optimum is $x_{s_a}=1/2$, $x_{s_b}=0$, $x_{\text{fict}}=1/2$. Either maximizing bundle leads to a rejection: $s_a$ is infeasible and the fictitious bundle is a rejection. Online therefore earns $3$, while Offline earns $3+1=4$ by allocating $s_a$ and then $s_b$. The regret is $1>0$ for every $\kappa>0$. The error comes from the fractional LP solution: (16) is not integral for bundles, so a fluid optimum can reserve half a unit for a bundle that can never be served.
--
--   **Formalization Note** The negated proposition is the full-strength reading of Theorem 5 that this mission drafted: arrival laws are arbitrary distributions on $[n]^T$, Eq. (17) is the All-Time Deviation bound with $\kappa_j=\kappa(|S_j|+1)/2$ (where $|S_j|=m_j$ counts the real bundles), the norm is a Mathlib `Seminorm` with definiteness, and the bundles of each type are distinct. The counterexample does not use any of these readings at an edge: it holds for every norm and every $\kappa>0$, and its rewards are nonnegative.
--
--   Differences from the source:
--   - correction: Theorem 5 "there exists a constant $\kappa$ … the expected regret … is at most $r_{\max}\sum_j p_j(c_j+\tau_j)$" → Lean: the negation of that statement; reason: the claim is false (the counterexample above satisfies every hypothesis, has bound $0$ and regret $1$); see DISPROOF.md.
--   - reading: "$\kappa$ depends on $(S_j:j\in[n])$ only" → Lean (inside the negated claim): $\kappa$ is chosen after the bundles and the norm $\mu$; reason: Eq. (17) uses $\kappa=\kappa_\mu(A)$, "which depends only on $A$ and $\mu$" (p. 26). The counterexample works for every $\kappa>0$.
--   - reading: $|S_j|$ in Eq. (17) → Lean (inside the negated claim): $m_j$, the number of real bundles; reason: p. 27, "there are $|S_j|+1$ possible bundles" once the fictitious item is included.
--   - reading: bundle rewards → Lean (inside the negated claim): $r_{sj}\ge0$; reason: rewards are gains of allocations (Sec. 2.1). The counterexample has positive rewards.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 26, Theorem 5 (with Eq. (16), Eq. (17), Algorithm 4, p. 26; proof sketch p. 27)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals
import Definitions.Def_BayesProphet_MultiSec_Supplement_Allocation

namespace BayesProphet.MultiSec.Supplement

theorem allocation_regret_counterexample :
    ¬ ∀ (d n : ℕ) [NeZero n] (m : Fin n → ℕ) (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ),
      (∀ j, Function.Injective (bund j)) →
      ∀ μ : Seminorm ℝ (Fin n → ℝ), (∀ y, μ y = 0 → y = 0) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (rew : (j : Fin n) → Fin (m j) → ℝ), (∀ j s, 0 ≤ rew j s) →
        ∀ (T : ℕ) (w : (Fin T → Fin n) → ℝ), IsArrivalLaw w →
        ∀ (c : Fin n → ℝ) (τ : Fin n → ℕ) (p : Fin n → ℝ),
          AllTimeDeviation w μ (fun j => κ * ((m j : ℝ) + 1) / 2) c τ →
          (∀ j, ∀ t ∈ Finset.Icc 1 T, probL w (fun θ => θ t = j) ≤ p j) →
        ∀ (B : Fin d → ℕ)
          (X : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j)) → ℝ),
          IsAllocFluidSelection bund rew w X →
        ∀ K : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j)),
          IsAllocArgmaxSelection X K →
          allocationExpectedRegret bund rew w K B ≤
            allocRmax rew * ∑ j, p j * (c j + τ j) := by sorry

end BayesProphet.MultiSec.Supplement
