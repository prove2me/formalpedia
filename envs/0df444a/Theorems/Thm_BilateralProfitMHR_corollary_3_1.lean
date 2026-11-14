-- Prove2me | Theorems.Thm_BilateralProfitMHR_corollary_3_1
-- name    : BilateralProfitMHR.corollary_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:27.815202+00:00
-- url     : https://prove2.me/theorems/aad8a1ca-251e-4f9d-ba99-e0415d016602
-- title:
--   Corollary 3.1 (Lattimore–György) — stochastic convex bandits with $O((1+\gamma)\sqrt n\log^2 n)$ expected regret
-- statement:
--   This is the paper's corollary of Theorem 1 of Lattimore and György, *Improved regret for zeroth-order stochastic convex bandits* (COLT 2021).
--
--   Let $\mathcal K\subseteq\mathbb R^d$ be a known convex body (nonempty, compact, convex), and let $L:\mathcal K\to\mathbb R$ be continuous and convex with values in a known interval $[b,b+\ell]$. Querying $x_\tau\in\mathcal K$ returns $L(x_\tau)+\xi_\tau$, where, conditional on the previous queries and observations and on $x_\tau$, the noise $\xi_\tau$ has mean zero and $\psi_2$ norm at most a known $\gamma\ge0$. Then there is a constant $C$ depending only on $d$ and $\ell$ such that for every $n\ge2$ there is an $n$-query algorithm with
--   $$\mathbb E\Big[\sum_{\tau=1}^n\big(L(x_\tau)-\min_{x\in\mathcal K}L(x)\big)\Big]\le C\,(1+\gamma)\sqrt n\,\log^2 n,$$
--   the expectation being over the noise and the algorithm's randomness. The algorithm may depend on $\mathcal K$, $b$, $\ell$, $\gamma$ and $n$, but not on $L$ or on the noise.
--
--   This is the routine ConOpt that the MHR algorithm runs on the loss $-\log\mu$.
--
--   Differences from the source:
--   - reading: "for every $n\ge1$ … $\in O((1+\gamma)\sqrt n\log^2(n))$" → there is $C$ with the bound for every $n\ge2$; reason: at $n=1$ the right side is $0$ and the claim is false: with $d=1$, $\mathcal K=[0,1]$, $\gamma=0$, interval $[0,1]$, the losses $L(x)=x$ and $L(x)=1-x$ give $\mathbb E[x_1]$ and $1-\mathbb E[x_1]$, one of which is at least $1/2$; for $n\ge2$ the constant absorbs small $n$ (regret is at most $\ell n$)
--   - encoding: "of constant dimension … depends only on the affine dimension and the length of the specified interval" → $\mathcal K\subseteq\mathbb R^d$ and $C$ depends on $d$ and $\ell$; reason: for fixed $d$ the affine dimension takes finitely many values, so the largest of their constants serves
--   - reading: "conditional on previous queries and observations, and on $x_\tau$, $\xi_\tau$ has mean zero and $\psi_2$ norm at most $\gamma$" → the observation law is a measurable kernel in the past queries, past observations and the current query, with mean $L(x)$ and $\psi_2$ norm of the centered observation at most $\gamma$ for every history with queries in $\mathcal K$; the noise depends on the learner's seed only through the queries; reason: conditional laws on $\mathbb R$ are kernels, a condition holding almost surely can be imposed everywhere by changing the kernel on a null set, and the learner's private randomness is independent of the environment in the bandit protocol
--   - encoding: "known" $\mathcal K$, interval and $\gamma$; "convex body"; $\min_{\mathcal K}L$; the expectation → the algorithm is chosen after $\mathcal K,b,\ell,\gamma,n$ and before $L$ and the noise; nonempty compact convex (lower-dimensional allowed); the infimum of $L$ on $\mathcal K$ (attained); a $[0,\infty]$-valued nested integral over the seed and the observations; reason: what "known" and "unknown" mean; the proof treats lower-dimensional bodies in their affine hull; the summands are nonnegative
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Corollary 3.1, pp.10–11 (PDF 12–13), restated p.30 (PDF 32); proof App. A.5, pp.58–59 (PDF 60–61). Cited from T. Lattimore and A. György, Improved regret for zeroth-order stochastic convex bandits, COLT 2021, PMLR 134:2938–2964, Theorem 1

import Mathlib
import Definitions.Def_BilateralProfitMHR_ConvexBandit

namespace BilateralProfitMHR

open MeasureTheory

/-- **Corollary 3.1 (Stochastic convex bandit)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), pp.10–11 (PDF 12–13), restated p.30 (PDF 32), proof App. A.5,
pp.58–59 (PDF 60–61); a corollary of Lattimore and György, *Improved regret for zeroth-order
stochastic convex bandits*, COLT 2021, PMLR 134:2938–2964, Theorem 1.

Let `𝒦` be a known convex body of constant dimension and `L : 𝒦 → ℝ` continuous and convex with
values in a known interval of constant length. Suppose querying `x_τ ∈ 𝒦` returns
`L(x_τ) + ξ_τ`, where, conditional on previous queries and observations and on `x_τ`, `ξ_τ` has
mean zero and `ψ₂` norm at most a known `γ ≥ 0`. Then for every `n` there is an `n`-query
algorithm with `E[∑_{τ=1}^n (L(x_τ) − min_{x∈𝒦} L(x))] ∈ O((1 + γ) √n log²(n))`, the hidden
constant depending only on the dimension and the length of the interval.

**Formalization Note.** The ambient space is `ℝ^d` (`EuclideanSpace ℝ (Fin d)`); the constant `C`
depends on `d` and on the interval length `ℓ` only. A convex body is a nonempty compact convex
set (lower-dimensional bodies allowed, as in the proof). The algorithm may depend on the known
data `𝒦`, `b`, `ℓ`, `γ`, `n`; the loss `L` and the environment `ν` (any measurable kernel
satisfying the noise condition, `NoiseCond`) are quantified after it. `O(·)` is read as `∃ C`
for every `n ≥ 2` (at `n = 1` the right side is `0` and the claim fails). `min_{𝒦} L` is
`sInf (L '' 𝒦)`, attained since `L` is continuous on the compact `𝒦`. The expectation over the
seed and the observations is `expectedCumLoss`, in `ℝ≥0∞`. Logarithms are natural. -/
theorem corollary_3_1 :
    ∀ (d : ℕ) (ℓ : ℝ), 0 < ℓ → ∃ C : ℝ, ∀ (K : Set (EuclideanSpace ℝ (Fin d))),
      K.Nonempty → IsCompact K → Convex ℝ K → ∀ (b γ : ℝ), 0 ≤ γ → ∀ n : ℕ, 2 ≤ n →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn L K → ConvexOn ℝ K L →
              (∀ x ∈ K, L x ∈ Set.Icc b (b + ℓ)) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable → NoiseCond K L γ ν →
                expectedCumLoss A P ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                  ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by sorry

end BilateralProfitMHR
