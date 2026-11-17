-- Prove2me | Theorems.Thm_CalibeatBandit_Supplement_theorem_5_1
-- name    : CalibeatBandit.Supplement.theorem_5_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T06:32:56.153764+00:00
-- url     : https://prove2.me/theorems/871016fb-0375-4710-8057-6e50f8296f0c
-- title:
--   Theorem 5.1 — continuous-price calibeating: $\mathbb E[\mathrm{SR}_T],\mathbb E[\mathrm{Rec}_T]\le\tilde O(T^{3/4}+K^{1/3}T^{2/3})$
-- statement:
--   Consider dynamic pricing over $T$ rounds with prices in $[0,1]$, production cost $c\in[0,1]$, non-increasing demand curves $D_t:[0,1]\to[0,1]$ and revenue $y_t(p)=(p-c)D_t(p)$. The recommendations are $K$-sparse: their supports lie in a common set of at most $K$ prices, unknown to the seller.
--
--   **Theorem.** For $K$-sparse recommendations and non-increasing demands, there is a dynamic pricing algorithm satisfying
--   $$\mathbb E[\mathrm{SR}_T],\ \mathbb E[\mathrm{Rec}_T]\le\tilde O\big(T^{3/4}+K^{1/3}T^{2/3}\big).$$
--   In other words, $(\varepsilon,\varepsilon)$-calibeating is achievable in $\tilde O(\varepsilon^{-4}+K\varepsilon^{-3})$ rounds.
--
--   Precisely:
--
--   1. There are constants $C>0$ and $k\in\mathbb N$ such that for all $K\ge1$, $T\ge1$ and $c\in[0,1]$ there is an admissible pricing algorithm with
--   $$\mathbb E[\mathrm{SR}_T]\le B,\quad \mathbb E[\mathrm{Rec}_T]\le B,\qquad B=C\big(T^{3/4}+K^{1/3}T^{2/3}\big)\big(1+\log(KT)\big)^k,$$
--   for every set of at most $K$ recommended prices in $[0,1]$ and every run of the pricing protocol.
--   2. There are constants $C'>0$ and $k'\in\mathbb N$ such that for all $K\ge1$, $c\in[0,1]$, $\varepsilon>0$ and
--   $$T\ge C'\big(\varepsilon^{-4}+K\varepsilon^{-3}\big)\big(1+\log K+|\log\varepsilon|\big)^{k'},$$
--   there is an admissible pricing algorithm with $\mathbb E[\mathrm{SR}_T]\le\varepsilon T$ and $\mathbb E[\mathrm{Rec}_T]\le\varepsilon T$.
--
--   The theorem carries the calibeating guarantee of Theorem 3.2 from finitely many actions to a continuum of prices. Theorem 5.2 of the paper shows the rate is optimal up to logarithmic factors.
--
--   **Formalization Note** The setting, the protocol and the benchmarks are `PricingRun`. The algorithm may depend on $K$, $T$ and $c$, but not on the set of recommended prices. It must be admissible: a measurable function of the seller's information whose values are probability measures on $[0,1]$. The expectations are outer expectations (`OuterExpLE`).
--
--   Differences from the source:
--
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean convention of the base mission; same instances
--   - reading: log → the natural logarithm `Real.log`; reason: p.7 fixes e as the base of the natural logarithm; the base mission uses the same convention
--   - reading: Õ(T^{3/4} + K^{1/3}T^{2/3}) and (ε, ε)-calibeating in Õ(ε^{−4} + Kε^{−3}) rounds → ∃ C > 0, k ∈ ℕ (before K, T, c): bound C(T^{3/4} + K^{1/3}T^{2/3})(1 + log(KT))^k; and ∃ C' > 0, k' ∈ ℕ: T ≥ C'(ε^{−4} + Kε^{−3})(1 + log K + |log ε|)^{k'} suffices for E[SR_T], E[Rec_T] ≤ εT; reason: Õ hides absolute constants and polylogarithmic factors; both clauses of the theorem are stated
--   - reading: prices p ∈ P ⊆ [0,1]; supremum over measurable maps σ : P → P → the seller posts prices in [0,1]; σ ranges over measurable maps ℝ → ℝ with values in [0,1] (only their restriction to [0,1] matters); reason: Theorem 5.1 is the continuous-price case P = [0,1] (§2.2: "a continuous price space"; App. E.1 compares against prices in [c,1] ⊆ [0,1])
--   - reading: K-sparse: a common set S with |S| ≤ K supports every q_t → a fixed map S : Fin K → [0,1] (its image has at most K points) and weights q_t on Fin K; the seller's algorithm is chosen before S; reason: the set is common to the run; the seller does not know it ("for K-sparse recommendations … there is a dynamic pricing algorithm")
--   - reading: there is a dynamic pricing algorithm → there is an admissible algorithm: a measurable kernel from the seller's information to probability measures on [0,1]; reason: the stronger reading; an algorithm is implementable, and a non-measurable rule could admit no runs and satisfy the bound vacuously
--   - encoding: E[SR_T], E[Rec_T] → outer expectations: some integrable g ≥ SR_T a.s. with E[g] ≤ the bound; reason: SR_T and Rec_T are suprema over uncountably many maps; the outer expectation is the expectation whenever they are measurable
--   - encoding: non-increasing demand D_t : [0,1] → [0,1] chosen by the adversary → D_t is jointly measurable in (ω, p) with respect to info t ⊗ Borel, non-increasing on [0,1] with values in [0,1]; reason: excludes only environments in which the observed revenue y_t(P_t) is not a random variable and its expectation is undefined
--   - encoding: the seller has access to the recommendation (§2.1) → the seller sees each recommended mixed strategy as a measure on prices and the drawn recommended price, as in the base protocol; reason: the base mission's convention (Algorithm 1 draws J_t itself); App. E.1's algorithm uses J_t
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Theorem 5.1, p.22 (PDF 22); setting §2.2, p.8 (PDF 8); proof in App. E.1, p.47 (PDF 47)

import Mathlib
import Definitions.Def_CalibeatBandit_Supplement_PricingRegretBound

set_option autoImplicit false

universe u

namespace CalibeatBandit

namespace Supplement

/-- **Theorem 5.1 (Continuous-price calibeating).** For `K`-sparse recommendations and
non-increasing demands, there is a dynamic pricing algorithm satisfying
`E[SR_T], E[Rec_T] ≤ Õ(T^{3/4} + K^{1/3}T^{2/3})`. In other words, `(ε, ε)`-calibeating is
achievable in `Õ(ε⁻⁴ + Kε⁻³)` rounds.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Theorem 5.1,
p.22; setting §2.2, p.8; proof in App. E.1, p.47.

**Formalization Note.** Two conjuncts, each with its `Õ` pinned by absolute constants chosen
before `K`, `T`, `c` (and `ε`):
1. there are `C > 0` and `k ∈ ℕ` such that for all `K ≥ 1`, `T ≥ 1` and `c ∈ [0, 1]` there is an
   admissible pricing algorithm (`IsPricingPolicy`: measurable, probability measures on `[0, 1]`)
   with `E[SR_T] ≤ B` and `E[Rec_T] ≤ B`, `B = C(T^{3/4} + K^{1/3}T^{2/3})(1 + log(KT))^k`, for
   every set `S ⊆ [0, 1]` of at most `K` recommended prices and every run of the pricing protocol;
2. there are `C' > 0` and `k' ∈ ℕ` such that for all `K ≥ 1`, `c ∈ [0, 1]`, `ε > 0` and
   `T ≥ C'(ε⁻⁴ + Kε⁻³)(1 + log K + |log ε|)^{k'}` there is an admissible algorithm with
   `E[SR_T] ≤ εT` and `E[Rec_T] ≤ εT` (Definition 2.2).
The algorithm may depend on `K`, `T` and `c`, not on `S`. Expectations are outer expectations
(`OuterExpLE`); `log` is `Real.log`. -/
theorem theorem_5_1 :
    (∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (K T : ℕ) (c : ℝ), 1 ≤ K → 1 ≤ T → c ∈ Set.Icc (0 : ℝ) 1 →
      ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
        PricingRegretBound.{u} K T c
          (C * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) *
            (1 + Real.log (K * T)) ^ k)
          (C * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) *
            (1 + Real.log (K * T)) ^ k)
          seller) ∧
    (∃ C' : ℝ, 0 < C' ∧ ∃ k' : ℕ, ∀ (K T : ℕ) (c ε : ℝ), 1 ≤ K → c ∈ Set.Icc (0 : ℝ) 1 → 0 < ε →
      C' * (ε⁻¹ ^ 4 + K * ε⁻¹ ^ 3) * (1 + Real.log K + |Real.log ε|) ^ k' ≤ T →
      ∃ seller : PricingPolicy, IsPricingPolicy seller ∧
        PricingRegretBound.{u} K T c (ε * T) (ε * T) seller) := by sorry

end Supplement

end CalibeatBandit
