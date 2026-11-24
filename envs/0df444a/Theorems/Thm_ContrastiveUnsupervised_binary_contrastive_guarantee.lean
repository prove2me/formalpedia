-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_binary_contrastive_guarantee
-- name    : ContrastiveUnsupervised.binary_contrastive_guarantee
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:08:18.729645+00:00
-- url     : https://prove2.me/theorems/554a3c27-b792-4c00-aeab-67c8adf9fb79
-- title:
--   Theorem 4.5 (as proved): guaranteed average binary classification
-- statement:
--   Let $\mathcal C$ be a countable set of latent classes with distribution $\rho$ and class distributions $\mathcal D_c$, and let $\tau=\sum_c\rho(c)^2<1$. Let $\ell$ be the hinge or the logistic loss. Let $\mathcal F$ be a pointwise separable class of measurable $f:\mathcal X\to\mathbb R^d$ with $\|f(\cdot)\|\le R$, $R>0$. Let $\widehat f$ be an empirical minimizer, $\widehat f(\mathcal S)\in\operatorname{argmin}_{f\in\mathcal F}\widehat L_{un}(f)$ for every training set $\mathcal S$ of $M\ge1$ tuples $(x,x^+,x^-)$ (one negative sample). There are absolute constants $K$ and $c'>0$ such that, for every $0<\delta\le1/2$, with probability at least $1-\delta$ over the training set $\mathcal S$ of $M\ge1$ tuples drawn from $(\mathcal D_{sim}\times\mathcal D_{neg})^M$, for all $f\in\mathcal F$,
--
--   $$L_{sup}(\widehat f)\le L^\mu_{sup}(\widehat f)\le L^{\ne}_{un}(f)+\beta\,s(f)+\eta\,Gen_M,$$
--
--   where $\beta=c'\frac{\tau}{1-\tau}$, $\eta=\frac{1}{1-\tau}$, $Gen_M=K\big(R\,\mathcal R_{\mathcal S}(\mathcal F)/M+R^2\sqrt{\log(1/\delta)/M}\big)$, $L^{\ne}_{un}(f)$ is the unsupervised loss conditioned on $c^+\ne c^-$, and $s(f)$ is the intraclass deviation.
--
--   This is the paper's main guarantee: if some $f\in\mathcal F$ contrasts different classes well and is concentrated within classes, the empirical minimizer of the contrastive loss does well on average binary classification.
--
--   **Formalization Note** $L_{sup}$ and $L^\mu_{sup}$ are averages over pairs of distinct classes with uniform label distribution, and $L_{sup}$ uses the best linear classifier. The paper's $O(\cdot)$ is an absolute constant $K$, and "with probability at least $1-\delta$" means that the outer measure of the failure set is at most $\delta$. The statement is restricted to $\delta\le1/2$ because the proof (Mohri et al., Theorem 3.1, and Hoeffding) produces $\log(4/\delta)$ and $\log(2/\delta)$. These are $O(\log(1/\delta))$ only for $\delta$ bounded away from $1$; for $\delta\le1/2$ the two forms agree up to the constant. Pointwise separability of $\mathcal F$ and measurability of each $f$ are standing conventions the paper does not state. The hypothesis $\tau<1$ is implicit in the paper's division by $1-\tau$.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 4.2, Theorem 4.5, p. 5

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem binary_contrastive_guarantee :
    ∃ K c' : ℝ, 0 < c' ∧
      ∀ {X : Type u} [MeasurableSpace X] {C : Type v} [Countable C] {d : ℕ}
      (D : C → Measure X) (ρ : C → ℝ), IsLatentClassModel D ρ → collisionProb ρ < 1 →
      ∀ (hinge : Bool) (R : ℝ), 0 < R →
      ∀ (F : Set (X → Rep d)), (∀ f ∈ F, IsBoundedRep f R) → IsPointwiseSeparable F →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (fhat : (Fin M → X × X × (Fin 1 → X)) → X → Rep d),
        (∀ S, fhat S ∈ F ∧ ∀ f ∈ F, empUnsupLoss hinge 1 (fhat S) S ≤ empUnsupLoss hinge 1 f S) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
        sampleMeasure D ρ 1 M {S | ¬ ∀ f ∈ F,
            avgSupLoss (stdLoss hinge) D ρ 1 (fhat S) ≤
                avgMeanSupLoss (stdLoss hinge) D ρ 1 (fhat S) ∧
              avgMeanSupLoss (stdLoss hinge) D ρ 1 (fhat S) ≤
                unsupLossNeq hinge D ρ 1 f +
                  c' * (collisionProb ρ / (1 - collisionProb ρ)) * intraclassDeviation D ρ f +
                  1 / (1 - collisionProb ρ) * genError K R 1 M (rademacherAvg F S) δ} ≤
          ENNReal.ofReal δ := by sorry

end ContrastiveUnsupervised
