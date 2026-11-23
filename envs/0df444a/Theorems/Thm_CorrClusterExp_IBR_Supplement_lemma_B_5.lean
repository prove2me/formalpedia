-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_Supplement_lemma_B_5
-- name    : CorrClusterExp.IBR.Supplement.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:27:55.979662+00:00
-- url     : https://prove2.me/theorems/53eec493-5487-4e03-84de-5ef97f475ce4
-- title:
--   Lemma B.5, p. 50 — perturbing the logarithmic partition: Ṽ^LB ≤ V^LB and 0 ≤ V − Ṽ ≤ n^{−δ1}Σwᵢ² + (α² − 1)Σwᵢ²
-- statement:
--   Let $0<q\le\tfrac12$, let $w_1\ge\dots\ge w_n\ge0$ be sorted cluster sizes and $\delta_1,\delta_2\in(0,1)$. Take the logarithmic partition of §4.2.2 with these parameters, with $\alpha=1+n^{-\delta_2}$, and let $V$ be the worst-case variance of its IBR experiment and $V^{\mathrm{LB}}$ the optimal value of (5).
--
--   Form the **perturbed instance**: drop block zero, and in each block $k\in[K]$ lower every cluster size to the block's smallest size $\underline w_k=\min_{i\in S_k}w_i$. Let $\tilde V$ be the worst-case variance of the IBR experiment of the perturbed instance with blocks $1,\dots,K$, and $\tilde V^{\mathrm{LB}}$ its optimal value of (5). Then
--   $$
--   \tilde V^{\mathrm{LB}}\le V^{\mathrm{LB}}\qquad\text{and}\qquad 0\le V-\tilde V\le n^{-\delta_1}\sum_{i=1}^nw_i^2+(\alpha^2-1)\sum_{i=1}^nw_i^2 .
--   $$
--
--   In the proof of Theorem 4.10 this lemma reduces the analysis to the perturbed instance, in which every block consists of equal sizes, so that the argument of Theorem 4.9 applies to it.
--
--   **Formalization Note** The partition, the perturbed sizes and the blocks $1,\dots,K$ are `logPartition`, `perturbedSizes` and `greedyBlocks` of the supplement's definition file; $V$, $\tilde V$ are the published `VIBR` and $V^{\mathrm{LB}},\tilde V^{\mathrm{LB}}$ the published `VLB`. The perturbed instance has the $n-n_0$ clusters outside block zero.
--
--   Differences from the source:
--   - generalization: the paper defines $[n]$ for positive $n$ → $n$ may also be zero; reason: the empty instance has an empty partition, both optimal values and both IBR variances are zero, and every conclusion reduces to $0\le0$; every positive-size source instance is retained.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 50, Lemma B.5 (perturbed instance: App. B.10, p. 50; logarithmic partition: §4.2.2, p. 26)

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
import Definitions.Def_CorrClusterExp_IBR_Supplement_LogPartition

namespace CorrClusterExp.IBR.Supplement

open Finset

theorem lemma_B_5 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1) :
    VLB (perturbedSizes w δ₁ δ₂) ≤ VLB w ∧
      0 ≤ VIBR q w (logPartition w δ₁ δ₂) -
        VIBR q (perturbedSizes w δ₁ δ₂) (greedyBlocks w δ₁ δ₂) ∧
      VIBR q w (logPartition w δ₁ δ₂) -
          VIBR q (perturbedSizes w δ₁ δ₂) (greedyBlocks w δ₁ δ₂) ≤
        (n : ℝ) ^ (-δ₁) * ∑ i, w i ^ 2 + (alpha n δ₂ ^ 2 - 1) * ∑ i, w i ^ 2 := by sorry

end CorrClusterExp.IBR.Supplement
