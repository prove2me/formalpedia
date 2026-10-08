-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_lemma_10_1
-- name    : BertsekasShreve.ImperfectInfo.lemma_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:41:33.088412+00:00
-- url     : https://prove2.me/theorems/5c73bd50-7af1-4aa7-96b2-9c7b86eaa3be
-- title:
--   Lemma 10.1 — under a Markov (PSI) policy, $V_{p,k}$ carries $P_k(\hat\pi,p)$ to $\hat P_k[\hat\pi,\varphi(p)]$
-- statement:
--   Let an (ISI) model with horizon $N$ and a statistic $(\eta_0,\dots,\eta_{N-1})$ sufficient for control be given, with associated (PSI) model. Let $p\in P(S)$ and let $\hat\pi=(\hat\mu_0,\hat\mu_1,\dots)$ be a Markov (PSI) policy, used in (ISI) through $\mu_k(du\mid p;i_k)=\hat\mu_k(du\mid\eta_k(p;i_k))$. Then for $k=0,\dots,N-1$ and every Borel set $B\subseteq Y_0C_0\cdots Y_kC_k$,
--   $$P_k(\hat\pi,p)\big[V_{p,k}^{-1}(B)\big]=\hat P_k[\hat\pi,\varphi(p)](B),$$
--   where $V_{p,k}(x_0,z_0,u_0,\dots,x_k,z_k,u_k)=[\eta_0(p;i_0),u_0,\dots,\eta_k(p;i_k),u_k]$ and $\varphi(p)$ is the distribution (26) of $y_0=\eta_0(p;z_0)$.
--
--   In words: the statistic process $(\eta_0,u_0,\dots,\eta_k,u_k)$ generated in (ISI) by $\hat\pi$ has exactly the law of the state–control process of (PSI) under the same policy started from $\varphi(p)$. This is the measure-level identity behind Proposition 10.2.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 253, Lemma 10.1 (Eq. (29) of Chapter 10)

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Lemma 10.1 (p. 253). -/
theorem lemma_10_1 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (p : ProbabilityMeasure S) (μ : (k : ℕ) → Y k → ProbabilityMeasure C)
    (hμ : σ.IsMarkovPolicy μ) (k : ℕ) (hk : k < M.N) (B : Set (Hist Y C k))
    (hB : MeasurableSet B) :
    M.law (σ.toISI μ) p k (σ.V p k ⁻¹' B) = σ.lawHat (markovToPolicy μ) (σ.phi p) k B := by sorry

end BertsekasShreve.ImperfectInfo
