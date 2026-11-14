-- Prove2me | Theorems.Thm_BilateralProfitRegular_corollary_3_1
-- name    : BilateralProfitRegular.corollary_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:14.073927+00:00
-- url     : https://prove2.me/theorems/70c79663-d801-4917-8ffa-d2216cc1bf1f
-- title:
--   Corollary 3.1 — stochastic convex bandits: $O((1+\gamma)\sqrt n\log^2 n)$ regret (cited from Lattimore–György)
-- statement:
--   This is the stochastic convex bandit bound the paper takes from Lattimore and György (*Improved regret for zeroth-order stochastic convex bandits*, COLT 2021, Theorem 1). Its algorithm is called ConOpt.
--
--   Fix an affine dimension $k$ and a length $\ell>0$. There is a constant $C$ with the following property. Let:
--
--   1. $\mathcal K\subseteq\mathbb R^d$ (any $d$) be nonempty, compact and convex, of affine dimension at most $k$;
--   2. $b\in\mathbb R$, $\gamma\ge0$, and $n\ge2$.
--
--   Then there is an $n$-query algorithm on $\mathcal K$ such that the following holds for every continuous convex $L:\mathcal K\to[b,b+\ell]$ and every noisy oracle returning $L(x_\tau)+\xi_\tau$, where $\xi_\tau$, conditional on the previous queries and observations and on $x_\tau$, has mean zero and $\|\xi_\tau\|_{\psi_2}\le\gamma$:
--   $$\mathbb E\Big[\sum_{\tau=1}^n\big(L(x_\tau)-\min_{x\in\mathcal K}L(x)\big)\Big]\le C(1+\gamma)\sqrt n\,\log^2 n.$$
--
--   The expectation is over the noise and the algorithm's randomness. The algorithm may depend on $\mathcal K,b,\ell,\gamma,n$ but not on $L$ or on the noise law. In the paper this result is applied to the scaled loss $\delta/r_\lambda$, which gives eq. (55).
--
--   **Formalization Note** $\|\cdot\|_{\psi_2}$ is the published sub-Gaussian norm, valued in $[0,\infty]$, with value $\infty$ for a non-subgaussian variable. Logarithms are natural.
--
--   Differences from the source:
--   - reading: "for every $n\ge1$ … $\in O((1+\gamma)\sqrt n\log^2(n))$" → every $n\ge2$, with one constant $C$; reason: at $n=1$ the right side is $0$ and the claim is false ($d=1$, $\mathcal K=[0,1]$, $\gamma=0$, $L(x)=x$ or $1-x$: one of the two has expected regret $\ge1/2$); $O(\cdot)$ is asymptotic in $n$, and for $n\ge2$ the finitely many small $n$ are absorbed since the regret is at most $\ell n$
--   - reading: "a known convex body of constant dimension"; "the hidden constant depends only on the affine dimension and the length of the specified interval" → $\mathcal K\subseteq\mathbb R^d$ (any ambient $d$) nonempty, compact, convex, with $\dim\operatorname{span}(\mathcal K-\mathcal K)\le k$ (possibly lower-dimensional); $C$ depends only on $k$ and $\ell$; reason: the proof (p.58) treats affine dimension $0$ and works in the affine hull, so a convex body need not be full-dimensional; a bound $\le k$ instead of $=k$ is equivalent (take the largest of the finitely many constants)
--   - encoding: noise conditional on previous queries and observations and on $x_\tau$, with mean zero and $\psi_2$ norm at most $\gamma$ → Markov kernels from (history, query) to the observation law, with mean $L(x)$ and $\|Y-L(x)\|_{\psi_2}\le\gamma$ at every history and every $x\in\mathcal K$; expectation by nested integration; reason: kernel form of the conditional laws of the process
--   - encoding: "known" $\mathcal K$, interval and $\gamma$; unknown $L$ → the algorithm is chosen after $\mathcal K,b,\gamma,n$ and before $L$ and the environment; reason: what the algorithm may depend on
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Corollary 3.1, p.30 (PDF 32; also p.10 and p.58); proof App. A.5, pp.58–59 (PDF 60–61); cited: T. Lattimore, A. György, Improved regret for zeroth-order stochastic convex bandits, COLT 2021, PMLR 134:2938–2964, Theorem 1

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Definitions.Def_BilateralProfitRegular_ConvexBandit

namespace BilateralProfitRegular

open MeasureTheory

/-- **Corollary 3.1 (Stochastic convex bandit)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.30 (PDF 32; also p.10 and p.58); a corollary of Theorem 1 of
T. Lattimore and A. György, *Improved regret for zeroth-order stochastic convex bandits*, COLT
2021, PMLR 134:2938–2964 (proof in App. A.5, pp.58–59).

Let `𝒦` be a known convex body of constant dimension and `L : 𝒦 → ℝ` continuous and convex with
values in a known interval `[b, b + ℓ]` of constant length. Querying `x_τ ∈ 𝒦` returns
`L(x_τ) + ξ_τ`, where, conditional on the previous queries and observations and on `x_τ`, `ξ_τ`
has mean zero and `ψ₂` norm at most a known `γ ≥ 0`. Then for every `n` there is an `n`-query
algorithm with `E[∑_{τ=1}^n (L(x_τ) − min_{x∈𝒦} L(x))] ≤ C (1 + γ) √n log²(n)`, the constant
depending only on the affine dimension and the length `ℓ`.

**Formalization Note.** `𝒦 ⊆ ℝ^d` (`Fin d → ℝ`, any ambient `d`) nonempty, compact and
convex, of affine dimension at most `k` (`finrank (vectorSpan 𝒦) ≤ k`; possibly
lower-dimensional, as the proof allows); `C` depends only on `k` and `ℓ`, not on the ambient `d`
("the hidden constant depends only on the affine dimension and the length"). The algorithm may depend on
the known data `𝒦, b, γ, n` (and `ℓ`), and is chosen before the unknown `L` and environment. The
environment is any sequence of Markov kernels giving the observation law from the past and the
current query, with conditional mean `L(x)` and `‖Y − L(x)‖_{ψ₂} ≤ γ` (the published `ψ₂` norm,
`⊤` for a non-subgaussian variable). `n ≥ 2`: at `n = 1` the right side is `0` and the claim
fails. Natural logarithm. -/
theorem corollary_3_1 :
    ∀ (k : ℕ) (ℓ : ℝ), 0 < ℓ → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (K : Set (Fin d → ℝ)), K.Nonempty → IsCompact K → Convex ℝ K →
      Module.finrank ℝ (vectorSpan ℝ K) ≤ k →
      ∀ (b : ℝ) (γ : NNReal) (n : ℕ), 2 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (alg : BanditAlg (Fin d → ℝ) Ω),
        alg.QueriesIn K ∧
        ∀ L : (Fin d → ℝ) → ℝ, ContinuousOn L K → ConvexOn ℝ K L →
          (∀ x ∈ K, b ≤ L x ∧ L x ≤ b + ℓ) →
          ∀ ν : ObsEnv (Fin d → ℝ), ν.MeanOn L K →
            (∀ τ h, ∀ x ∈ K,
              HighDimProb.Concentration.subgaussianNorm (ν τ (h, x)) (fun y => y - L x) ≤ γ) →
            alg.regret ν Pω n L K ≤
              ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by sorry

end BilateralProfitRegular
