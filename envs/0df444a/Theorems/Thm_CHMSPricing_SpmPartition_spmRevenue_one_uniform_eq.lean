-- Prove2me | Theorems.Thm_CHMSPricing_SpmPartition_spmRevenue_one_uniform_eq
-- name    : CHMSPricing.SpmPartition.spmRevenue_one_uniform_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:43:57.393439+00:00
-- url     : https://prove2.me/theorems/ef7667af-e17c-4eda-9263-f5f9fe53f802
-- title:
--   App. C.2, p. 14 — under a single unit the SPM revenue is Σ_k Π_{j<k}(1 − q_j) p_k q_k
-- statement:
--   Consider a seller with a single unit (the $1$-uniform matroid) and a sequential posted-price mechanism with ordering $\sigma$ and arbitrary real prices $p_i$. Number the agents by their position in the offer order, so that the $k$-th agent in line is $\sigma(k)$, and let $q_k=1-F_{\sigma(k)}(p_{\sigma(k)})$ be the probability that this agent accepts its price. Then the expected revenue is
--
--   $$
--   \mathcal R^\sigma_{\mathbf p}=\sum_{k=0}^{n-1}c_k\,p_{\sigma(k)}\,q_k,\qquad c_k=\prod_{j<k}(1-q_j),
--   $$
--
--   where $c_k$ is the probability that the $k$-th agent is offered the unit, i.e. that no earlier agent accepted.
--
--   This formula turns the revenue of the SPM in the single-unit case into an explicit function of the acceptance probabilities and prices; the subsequent comparisons (Lemma 20 and display (3)) are inequalities about it.
--
--   **Formalization Note** Positions are 0-based. The identity holds for every ordering and every real price vector; with the prices of the mechanism $\mathcal S$ one has $q_k=q^M_{\sigma(k)}$, which is the page's form $\sum_i c_i p^M_i q^M_i$. Values: each value distribution $F_i$ is given by a density $f_i$ that is measurable and strictly positive on a bounded interval $[\underline v_i,\bar v_i]$ with $0\le\underline v_i<\bar v_i$, integrates to $1$ there and puts no mass outside (the paper says only "distribution function $F_i$ with density $f_i$"); in particular there are no point masses, so $\Pr[p_i\le v_i]=1-F_i(p_i)$.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 14, App. C.2, first display (R^S = Σ_i c_i p^M_i q^M_i = Σ_i Π_{j<i}(1 − q_j) p^M_i q^M_i)

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem spmRevenue_one_uniform_eq {n : ℕ} (D : Fin n → ValueDist)
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) :
    spmRevenue D (uniformSystem (Fin n) 1) σ p =
      ∑ k : Fin n, oneUnitOfferProb (fun j => 1 - (D (σ j)).cdf (p (σ j))) k *
        p (σ k) * (1 - (D (σ k)).cdf (p (σ k))) := by sorry

end CHMSPricing.SpmPartition
