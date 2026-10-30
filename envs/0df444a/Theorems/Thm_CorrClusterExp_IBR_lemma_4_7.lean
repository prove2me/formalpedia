-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_lemma_4_7
-- name    : CorrClusterExp.IBR.lemma_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:05.023809+00:00
-- url     : https://prove2.me/theorems/1d8db6dc-a25b-4035-a0d6-732567af8ed2
-- title:
--   Lemma 4.7, p. 23 — f_q(k) ≤ ¼(k + C(q)) with a constant C(q) depending only on q
-- statement:
--   Let $0<q\le\tfrac12$. There is a constant $C(q)$, depending only on $q$, such that for every integer $k\ge1$
--   $$
--   f_q(k)\le\frac14\big(k+C(q)\big),
--   $$
--   where $f_q(k)$ is the optimal value of (1) for $k$ clusters all of size one. Thus $f_q$ grows linearly in $k$ with slope $\tfrac14$; this is the rate used in the asymptotic analysis of §4.2.
--
--   Differences from the source:
--   - reading: "$C(q)$ is a constant that depends only on $q$" → $\exists\,C\in\mathbb R$ chosen after $q$ and before $k$; reason: the literal meaning of a constant depending only on $q$.
--   - encoding: $f_q(k)$ for $k$ clusters → $k\ge1$; reason: an instance needs at least one cluster.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 23, Lemma 4.7

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

theorem lemma_4_7 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → fq q k ≤ 1 / 4 * ((k : ℝ) + C) := by sorry

end CorrClusterExp.IBR
