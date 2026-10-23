-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_ibr_additivity
-- name    : CorrClusterExp.IBR.ibr_additivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:07.383267+00:00
-- url     : https://prove2.me/theorems/c2975e07-d0f0-4143-b27e-cb091742ca40
-- title:
--   §3.2, p. 16 — an IBR experiment is an experiment with marginals q, and its worst-case variance is the sum of the worst-case variances of its blocks
-- statement:
--   Let $0<q\le\tfrac12$, let $w_1,\dots,w_n\ge 0$ be cluster sizes, and partition the clusters into consecutive blocks $B_1,\dots,B_L$. Consider the IBR experiment that, independently on each block $B_j$ with $m_j$ clusters, treats a uniformly random set of $\lfloor qm_j\rfloor$ clusters with probability $p_j=\lceil qm_j\rceil-qm_j$ and of $\lceil qm_j\rceil$ clusters otherwise. Then every cluster is treated with probability $q$, and the worst-case variance of the IBR experiment is the sum of the worst-case variances of its blocks:
--   $$
--   \max_{y\in\times_{i\in[n]}[0,w_i]} y^\top\Sigma y=\sum_{j=1}^{L}\ \max_{y\in\times_{i\in B_j}[0,w_i]} y^\top\Sigma_j\, y ,
--   $$
--   where $\Sigma$ is the correlation matrix of the IBR experiment and $\Sigma_j$ that of the block law on $B_j$.
--
--   This additivity is what makes the optimal partition computable by the dynamic program (4).
--
--   **Formalization Note** Blocks are given by `c : Composition n`; block $j$ has `c.blocksFun j` clusters, embedded by `c.embedding j`.
--
--   Differences from the source:
--   - generalization: the page speaks of the worst-case variance only → Lean also concludes that the IBR law is an experiment (marginals $q$); reason: p. 14 states that IBR treats a fraction $q$ of each block; the added conclusion is needed for $V^{\mathrm{OPT}}\le V^{\mathrm{DP}}$ and dropping it gives the page's claim.
--   - generalization: blocks of the clusters sorted by decreasing size → any consecutive blocks of any $w\ge 0$, sorted or not; reason: the sizes play no role in additivity; the sorted case is an instance.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 16, §3.2 (unnumbered claim after Lemma 3.3); IBR experiment p. 14

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

open Matrix Finset

theorem ibr_additivity (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (c : Composition n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) :
    IsExperiment q (ibrLaw q c) ∧
      VIBR q w c = ∑ j : Fin c.length,
        worstCase (corr q (fracLaw q (c.blocksFun j))) (fun i => w (c.embedding j i)) := by sorry

end CorrClusterExp.IBR
