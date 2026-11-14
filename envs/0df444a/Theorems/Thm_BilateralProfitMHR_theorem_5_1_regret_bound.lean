-- Prove2me | Theorems.Thm_BilateralProfitMHR_theorem_5_1_regret_bound
-- name    : BilateralProfitMHR.theorem_5_1_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:17.186106+00:00
-- url     : https://prove2.me/theorems/ff1152f2-2055-4986-97d3-e6eadcba7c32
-- title:
--   Theorem 5.1 — one-bit feedback achieves regret $O(\sqrt T\log^{5/2}T)$ for independent MHR valuations
-- statement:
--   There exists a learning algorithm $\mathcal A$ with one-bit feedback such that, for every horizon $T$ and every pair $\mathcal D$ of independent MHR buyer and seller distributions on $[0,1]$ with strictly positive densities,
--   $$R_T(\mathcal A,\mathcal D)=\sup_{(p,q)\in[0,1]^2}\sum_{t=1}^T\mathbb E\big[\mathrm{Profit}_t(p,q)-\mathrm{Profit}_t(p_t,q_t)\big]\le O\big(\sqrt T\,(\log T)^{5/2}\big).$$
--
--   Precisely: there are a constant $C>0$, a probability space of seeds and, for every horizon $T$, a pricing policy that observes only the trade bit $z_t=\mathbb 1\{s_t\le p_t\}\mathbb 1\{q_t\le b_t\}$ of each round, all fixed in advance, such that for every $T\ge2$, every such $\mathcal D$ and every comparator $(p,q)\in[0,1]^2$ (including $p>q$),
--   $$\sum_{t=1}^T\Big(\mathbb E[\mathrm{Profit}_t(p,q)]-\mathbb E[\mathrm{Profit}_t(p_t,q_t)]\Big)\le C\sqrt T\,(\log T)^{5/2},$$
--   the expectations being over the i.i.d. valuations $(s_t,b_t)\sim\mathcal D$ and the algorithm's randomness. MHR means that the seller's hazard rate $f_s/F_s$ is nonincreasing on $(0,1]$ and the buyer's $f_b/(1-F_b)$ is nondecreasing on $[0,1)$.
--
--   This improves the $\tilde O(T^{2/3})$ regret of the adversarial setting to $\tilde O(\sqrt T)$ under the monotone hazard rate assumption, still with one-bit feedback.
--
--   **Formalization Note** Logarithms are natural; rounds are indexed $0,\dots,T-1$.
--
--   Differences from the source:
--   - reading: "there exists a learning algorithm $\mathcal A$ … for every $T$" → a family of policies indexed by the horizon $T$, with one seed space, fixed before $T$ and $\mathcal D$; reason: Algorithm 6 takes the horizon $T$ as input and sets $K$ from $T$
--   - encoding: $R_T\le O(\sqrt T(\log T)^{5/2})$ → there is $C>0$ with the bound $C\sqrt T(\log T)^{5/2}$ for every $T\ge2$; reason: at $T=1$ the right side is $0$; $O(\cdot)$ is asymptotic in $T$
--   - encoding: $\sup_{(p,q)\in[0,1]^2}$; $\log$; rounds $t=1,\dots,T$; the learner's private randomness → the bound for every comparator in $[0,1]^2$; the natural logarithm; rounds $0,\dots,T-1$; a seed drawn once from a probability space; reason: a supremum is at most $B$ iff every term is; the remaining items are notation
--   - encoding: "independent MHR buyer and seller distributions on $[0,1]$ with strictly positive densities" → the published bilateral trade environment with supports $[0,1]$ (independent values, measurable densities strictly positive on $[0,1]$ integrating to $1$) satisfying Definition 2.3 for both agents; reason: §2's class exactly; the reused structure adds no condition
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Theorem 5.1, p.30 (PDF 32); proof §5.5, p.36 (PDF 38)

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

/-- **Theorem 5.1 (Regret for MHR distributions)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.30 (PDF 32): there exists a learning algorithm `𝒜` with
one-bit feedback such that, for every `T` and every pair `𝒟` of independent MHR buyer and seller
distributions on `[0, 1]` with strictly positive densities,
`R_T(𝒜, 𝒟) ≤ O(√T (log T)^{5/2})`.

There are a constant `C > 0`, a seed space `(Ω, P)` and, for every horizon `T`, a one-bit
policy `π T`, chosen before `T` and `𝒟`, such that for every `T ≥ 2`, every environment `E`
(independent values, densities strictly positive on `[0, 1]`, both MHR) and every comparator
`(p, q) ∈ [0, 1]²`,
`∑_{t=1}^T (E[Profit_t(p, q)] − E[Profit_t(p_t, q_t)]) ≤ C √T (log T)^{5/2}`, the expectations
being over the i.i.d. valuations with law `E.prior` and the seed.

**Formalization Note.** "A learning algorithm … for every `T`" is a family indexed by the
horizon (Algorithm 6 takes `T` as input and sets `K` from `T`), fixed before `T` and `𝒟`.
`O(·)` is `∃ C > 0` for every `T ≥ 2` (at `T = 1` the right side is `0`). The supremum over
comparators is a bound for every comparator. Logarithms are natural; rounds are `Fin T`. -/
theorem theorem_5_1_regret_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ π : (T : ℕ) → Policy T Ω, (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, UnitSupport E → IsMHR E →
          ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
            (π T).regret P E.prior (p, q) ≤
              C * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by sorry

end BilateralProfitMHR
