-- Prove2me | Theorems.Thm_BigDataNV_Reg_theorem2_generalization_bound
-- name    : BigDataNV.Reg.theorem2_generalization_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:28.662199+00:00
-- url     : https://prove2.me/theorems/82cd3bd1-cc5f-4d46-82c0-d7b863c472f4
-- title:
--   Theorem 2, p. 9 — w.p. ≥ 1 − δ, |R_true(q̂) − R̂(q̂; S_n)| ≤ (b∨h)²X²_max/(nλ) + (2(b∨h)²X²_max/λ + (b∨h)D̄)√(ln(2/δ)/2n)
-- statement:
--   Let $b,h>0$ be the unit backordering and holding costs of the newsvendor cost $C(q;d)=b(d-q)^+ + h(q-d)^+$, let $\lambda>0$, $X_{\max}\ge0$, $\bar D\ge0$, and let $n\ge1$. Features live in a domain $\mathcal X\subseteq\mathbb R^p$ with $\|x\|_2^2\le X_{\max}^2$ for all $x\in\mathcal X$, demands in $\mathcal D=[0,\bar D]$, and the data are drawn iid from a probability distribution $\mu$ concentrated on $\mathcal X\times\mathcal D$.
--
--   For each sample $S_n=\{(x_i,d_i)\}_{i=1}^n$ let $\hat q=\hat q(S_n)\in\mathbb R^p$ be a solution of (NV-reg),
--   $$\hat q\in\arg\min_{q\in\mathbb R^p}\ \frac1n\sum_{i=1}^n C(q^\top x_i;d_i)+\lambda\|q\|_2^2 ,$$
--   chosen measurably in $S_n$, and assume (Appendix B, $\mathcal Q\subset\mathcal D^{\mathcal X}$) that on samples from $\mathcal X\times\mathcal D$ the rule $x\mapsto\hat q^\top x$ maps $\mathcal X$ into $[0,\bar D]$. Let $R_{true}(q)=\mathbb E_{(x,d)\sim\mu}[C(q^\top x;d)]$ and $\hat R(q;S_n)=\frac1n\sum_i C(q^\top x_i;d_i)$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$ over $S_n$,
--   $$|R_{true}(\hat q)-\hat R(\hat q;S_n)|\le\frac{(b\vee h)^2X_{\max}^2}{n\lambda}+\Bigl(\frac{2(b\vee h)^2X_{\max}^2}{\lambda}+(b\vee h)\bar D\Bigr)\sqrt{\frac{\ln(2/\delta)}{2n}} .$$
--
--   The bound does not depend on the number of features $p$: regularization controls the generalization gap of the feature-based newsvendor rule in the high-dimensional regime.
--
--   **Formalization Note** Display (6) prints $\bar D$ as the last term inside the parenthesis; the proof (p. 32) combines Theorems 4 and 6 with the loss bound $M=(b\vee h)\bar D$ of Lemma 5, which gives $(b\vee h)\bar D$, and that constant is stated. The factors $X_{\max}^{-2}$ in the denominators of (6) are factors $X_{\max}^2$, and the feature ball is $\|x\|_2^2\le X_{\max}^2$. The failure event, on which the gap exceeds the bound, has probability at most $\delta$ under the product measure $\mu^n$. The range hypothesis is quantified only over feature vectors in $\mathcal X$ and samples from $\mathcal X\times\mathcal D$. Measurability of $S_n\mapsto\hat q(S_n)$ is the standing convention of Appendix B; it also follows from continuity of the unique minimizer. The convention of Appendix B that all sets are countable is dropped, and the intercept convention $x^1=1$ of §2.3 is not imposed; both generalize the statement.
-- source:
--   Rudin & Vahn, The Big Data Newsvendor: Practical Insights from Machine Learning, MIT Sloan Working Paper 5036-13 (version of February 6, 2014), p. 9, Theorem 2 and display (6); standing assumptions p. 9 (§3) and p. 27 (App. B); proof p. 32

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

open MeasureTheory FoundationsML.Stability

namespace BigDataNV.Reg

/-- Theorem 2, p. 9, display (6), with the constant `(b ∨ h) D̄` that its proof (p. 32) supplies
in place of the printed `D̄`: with probability at least `1 − δ` over an iid sample of size `n`,
the out-of-sample cost of the (NV-reg) rule differs from its in-sample cost by at most
`(b∨h)² X²_max /(nλ) + (2 (b∨h)² X²_max / λ + (b∨h) D̄) √(ln(2/δ)/(2n))`. -/
theorem theorem2_generalization_bound {p n : ℕ} (b h lam Xmax Dbar : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ Xmax) (hD : 0 ≤ Dbar)
    (Xdom : Set (EuclideanSpace ℝ (Fin p))) (hXdom : ∀ x ∈ Xdom, ‖x‖ ^ 2 ≤ Xmax ^ 2)
    (μ : Measure (EuclideanSpace ℝ (Fin p) × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (dataSupport Xdom Dbar)ᶜ = 0)
    (qhat : (Fin n → EuclideanSpace ℝ (Fin p) × ℝ) → EuclideanSpace ℝ (Fin p))
    (hqhat : ∀ S, IsNVRegSolution b h lam S (qhat S))
    (hrange : ∀ S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ, (∀ j, S j ∈ dataSupport Xdom Dbar) →
      ∀ x ∈ Xdom, inner ℝ (qhat S) x ∈ Set.Icc 0 Dbar)
    (hmeas : Measurable qhat)
    (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | (max b h) ^ 2 * Xmax ^ 2 / ((n : ℝ) * lam) +
          (2 * (max b h) ^ 2 * Xmax ^ 2 / lam + max b h * Dbar) *
            Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        |GeneralizationError μ (nvCost b h) (linEval (qhat S)) -
          EmpiricalError (nvCost b h) S (linEval (qhat S))|} ≤ ENNReal.ofReal δ := by sorry

end BigDataNV.Reg
