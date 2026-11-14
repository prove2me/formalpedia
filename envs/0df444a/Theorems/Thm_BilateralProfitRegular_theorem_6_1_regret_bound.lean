-- Prove2me | Theorems.Thm_BilateralProfitRegular_theorem_6_1_regret_bound
-- name    : BilateralProfitRegular.theorem_6_1_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:35.970751+00:00
-- url     : https://prove2.me/theorems/b8fd354d-7cd8-4951-b3bc-5a583d717253
-- title:
--   Theorem 6.1 — one-bit feedback achieves $O(T^{3/5}\log^5T)$ regret for independent regular valuations
-- statement:
--   There exist a learning algorithm $\mathcal A$ with one-bit feedback and a constant $C$ such that, for every horizon $T\ge2$ and every pair $\mathcal D$ of independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities,
--   $$R_T(\mathcal A,\mathcal D)=\sup_{(p,q)\in[0,1]^2}\sum_{t=1}^T\mathbb E\big[\mathrm{Profit}_t(p,q)-\mathrm{Profit}_t(p_t,q_t)\big]\le C\,T^{3/5}\log^5 T .$$
--
--   The expectation is over the i.i.d. valuations and the algorithm's randomness. The learner sees only the trade bit of each round. The comparator ranges over all of $[0,1]^2$, including $p>q$. The paper's proof gives the sharper $O(T^{3/5}\log^{7/2}T)$. Together with Theorem 7.1's $\Omega(T^{3/5})$ lower bound, the rate for regular distributions is $\tilde\Theta(T^{3/5})$.
--
--   **Formalization Note** The algorithm is a family of policies indexed by the horizon, on one seed space, chosen with $C$ before $T$ and $\mathcal D$. Logarithms are natural.
--
--   Differences from the source:
--   - reading: "a learning algorithm $\mathcal A$ … for every $T$" → a family $(\pi_T)_T$ of one-bit policies on one seed space, chosen (with $C$) before $T$ and the distributions; reason: the paper's algorithms take the horizon as input (Algorithms 7–8; "we choose $\eta$ as a function of $T$", p.37)
--   - encoding: $R_T\le O(T^{3/5}\log^5(T))$ → $\exists C>0$ with the bound $C\,T^{3/5}(\log T)^5$ for every $T\ge2$; reason: at $T=1$ the right side is $0$; $O(\cdot)$ is asymptotic in $T$
--   - encoding: $\sup_{(p,q)\in[0,1]^2}$ of the expected regret; the learner's randomness → the bound for every comparator in $[0,1]^2$; a seed drawn once from a probability space, valuations i.i.d. $\mathcal D$ independent of it; rounds $0,\dots,T-1$; natural log; reason: a supremum is at most $B$ iff every term is; standard model of a randomized policy
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Theorem 6.1, p.36 (PDF 38); proof §6.4, pp.46–49 (PDF 48–51)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

/-- **Theorem 6.1 (Regret for regular distributions)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.36 (PDF 38); proof pp.46–49 (PDF 48–51). There exists a learning
algorithm `𝒜` with one-bit feedback such that, for every `T` and every pair `𝒟` of independent
regular buyer and seller distributions on `[0, 1]` with strictly positive densities,
`R_T(𝒜, 𝒟) ≤ O(T^{3/5} log⁵(T))`.

**Formalization Note.**
* The algorithm is a horizon-indexed family `π T` of randomized one-bit policies on one seed
  space `(Ω, P)`, chosen (with the constant `C`) before `T` and the distributions: the paper's
  algorithms take the horizon `T` as input (Algorithms 7–8; `η` is chosen as a function of `T`).
* `O(·)` is a universal constant `C` for all `T ≥ 2` (at `T = 1` the right side is `0`).
* `R_T = sup_{(p,q) ∈ [0,1]²} ∑_t (E[Profit_t(p, q)] − E[Profit_t(p_t, q_t)])`; the bound is
  stated for every comparator in `[0,1]²`, which is equivalent.
* The distributions are a published `Environment` with supports `[0, 1]` and `E.Regular`
  (Definitions 2.1–2.2); the valuations are i.i.d. with law `E.prior`, independent of the seed.
  Natural logarithm; rounds `Fin T`. -/
theorem theorem_6_1_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (π : (T : ℕ) → Policy T Ω),
        (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, RegularUnit E →
          ∀ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            (π T).regret P E.prior a ≤ C * (T : ℝ) ^ ((3 : ℝ) / 5) * Real.log T ^ 5 := by sorry

end BilateralProfitRegular
