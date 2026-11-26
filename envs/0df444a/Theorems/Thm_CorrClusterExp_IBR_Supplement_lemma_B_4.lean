-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_Supplement_lemma_B_4
-- name    : CorrClusterExp.IBR.Supplement.lemma_B_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:26:44.754381+00:00
-- url     : https://prove2.me/theorems/0b4bfe6a-9176-459d-af9f-2a4089d9201d
-- title:
--   Lemma B.4, p. 50 — the term (a) of (17): h²(1/m + σ) − hσ ≤ 1/(2q(1−q)) + 1
-- statement:
--   Let $0<q\le\tfrac12$, let $m\ge1$ be the number of clusters in a block, and let $\sigma$ be the pairwise correlation of the block law of Proposition 3.1:
--   $$
--   p=\lceil qm\rceil-qm,\qquad \sigma=-\frac{mq(1-q)-p(1-p)}{m(m-1)q(1-q)}.
--   $$
--   Then for every integer $h$ with $0\le h\le m$,
--   $$
--   h^2\Big(\frac1m+\sigma\Big)-h\sigma\;\le\;\frac{1}{2q(1-q)}+1 .
--   $$
--
--   In the proof of Theorem 4.9 the left side is the term (a) of the chain (17), with $m=n_k$ the size of block $k$ and $h=\bar h_k$ the number of its clusters at their upper bound in the worst case of the IBR experiment. The bound is what turns (17) into the additive constant $\tfrac{2}{q(1-q)}+4$ of Theorem 4.9, and it is used again through (17) in the proof of Theorem 4.10.
--
--   **Formalization Note** $\sigma$ and $p$ are given by hypotheses fixing them to the closed form above. For $m=1$ the formula has a zero denominator, which Lean evaluates to $\sigma=0$; there the left side is $h^2\in\{0,1\}$, as in the paper's own case $n_k=1$.
--
--   Differences from the source:
--   - generalization: (a) is stated for the worst-case count $\bar h_k$ → for every integer $0\le h\le m$; reason: the paper's proof uses only $0\le\bar h_k\le n_k$, so the Lean statement specializes to the source's.
--   - encoding: σ_kk is "as given in Proposition 3.1" → the closed form of Proposition 3.1 (case 2, which reduces to $-1/(m-1)$ when $qm\in\mathbb N$) is a hypothesis, and at $m=1$ it evaluates to $0$; reason: the proof on p. 50 uses this closed form; at $m=1$ the source treats the case separately and the value of σ does not matter.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 50, Lemma B.4 (term (a) of (17), p. 49)

import Mathlib

namespace CorrClusterExp.IBR.Supplement

theorem lemma_B_4 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (m : ℕ) (hm : 1 ≤ m) (h : ℕ)
    (hh : h ≤ m) (p σ : ℝ) (hp : p = (⌈q * m⌉₊ : ℝ) - q * m)
    (hσ : σ = -((m * q * (1 - q) - p * (1 - p)) / (m * (m - 1) * q * (1 - q)))) :
    (h : ℝ) ^ 2 * (1 / (m : ℝ) + σ) - h * σ ≤ 1 / (2 * q * (1 - q)) + 1 := by sorry

end CorrClusterExp.IBR.Supplement
