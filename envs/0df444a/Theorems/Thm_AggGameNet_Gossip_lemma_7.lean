-- Prove2me | Theorems.Thm_AggGameNet_Gossip_lemma_7
-- name    : AggGameNet.Gossip.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:29.227614+00:00
-- url     : https://prove2.me/theorems/8e40cdf2-97b3-4573-84b3-bd03302db938
-- title:
--   Lemma 7, p. 17 — almost-sure update-count stepsize estimates
-- statement:
--   Let $G$ be connected and let $p_{ij}>0$ on every edge, with each contact-probability row summing to one. Independent tick pairs have law $\Pr(I^k=i,J^k=j)=p_{ij}/N$. Write $p_i=N^{-1}(1+\sum_jp_{ji})$ and $\hat p=1+\min_{(i,j):\{i,j\}\in\mathcal E}p_{ij}$. For any $0<q<1/2$, almost surely there is a path-dependent threshold after which, for every agent and integer $k\ge1$,
--
--   $$
--   \alpha_{k,i}\le\frac{2}{kp_i},\qquad
--   \left|\alpha_{k,i}-\frac1{kp_i}\right|\le
--   \frac{2}{k^{3/2-q}\hat p^2},
--   \qquad \alpha_{k,i}=\frac1{\Gamma_k(i)}.
--   $$
--
--   These rates control the stochastic stepsizes used in the convergence proof.
--
--   **Formalization Note** The printed lemma says “for every $\omega$,” but its appendix proves the almost-sure version. Lean counts ticks from zero, so $\Gamma_k(i)$ includes ticks $0,\ldots,k$. The positive-time bounds retain the paper's constants.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 7, p. 17 and appendix proof, pp. 39–41

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

namespace AggGameNet.Gossip

theorem lemma_7 {N : ℕ} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : GossipDraws P I J p)
    (phat : ℝ)
    (hphat : (∃ i j, G.Adj i j ∧ phat = 1 + p i j) ∧
      ∀ i j, G.Adj i j → phat ≤ 1 + p i j) :
    ∀ q : ℝ, 0 < q → q < 1 / 2 →
      ∀ᵐ ω ∂P, ∃ kt : ℕ, ∀ k : ℕ, kt ≤ k → 1 ≤ k → ∀ i : Fin N,
        alphaG I J k ω i ≤ 2 / ((k : ℝ) * pbar p i) ∧
        |alphaG I J k ω i - 1 / ((k : ℝ) * pbar p i)| ≤
          2 / ((k : ℝ) ^ ((3 : ℝ) / 2 - q) * phat ^ 2) := by sorry

end AggGameNet.Gossip
