-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_unsup_loss_upper_bound
-- name    : ContrastiveUnsupervised.unsup_loss_upper_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:07:57.442826+00:00
-- url     : https://prove2.me/theorems/b4bad4da-c293-4b15-acfd-f9e233023089
-- title:
--   Theorem 4.1 (as proved): upper bound using the unsupervised loss
-- statement:
--   Let $\mathcal C$ be a countable set of latent classes with distribution $\rho$ and class distributions $\mathcal D_c$, and let $\tau=\sum_c\rho(c)^2<1$. Let $\ell$ be the hinge or the logistic loss. Let $\mathcal F$ be a pointwise separable class of measurable $f:\mathcal X\to\mathbb R^d$ with $\|f(\cdot)\|\le R$, $R>0$. Let $\widehat f$ be an empirical minimizer, $\widehat f(\mathcal S)\in\operatorname{argmin}_{f\in\mathcal F}\widehat L_{un}(f)$ for every training set $\mathcal S$ of $M\ge1$ tuples $(x,x^+,x^-)$ (one negative sample). There is an absolute constant $K$ such that, for every $0<\delta\le1/2$, with probability at least $1-\delta$ over the training set $\mathcal S$ of $M\ge1$ tuples drawn from $(\mathcal D_{sim}\times\mathcal D_{neg})^M$, for all $f\in\mathcal F$,
--
--   $$L^\mu_{sup}(\widehat f)\le\frac{1}{1-\tau}\big(L_{un}(f)-\tau\big)+\frac{1}{1-\tau}Gen_M,\qquad Gen_M=K\Big(R\frac{\mathcal R_{\mathcal S}(\mathcal F)}{M}+R^2\sqrt{\frac{\log(1/\delta)}{M}}\Big).$$
--
--   If $\mathcal F$ contains a representation with small unsupervised loss, the learned representation has small average binary loss with the mean classifier.
--
--   **Formalization Note** The paper's $O(\cdot)$ is an absolute constant $K$, and "with probability at least $1-\delta$" means that the outer measure of the failure set is at most $\delta$. The statement is restricted to $\delta\le1/2$ because the proof (Mohri et al., Theorem 3.1, and Hoeffding) produces $\log(4/\delta)$ and $\log(2/\delta)$. These are $O(\log(1/\delta))$ only for $\delta$ bounded away from $1$; for $\delta\le1/2$ the two forms agree up to the constant. Pointwise separability of $\mathcal F$ and measurability of each $f$ are standing conventions the paper does not state. The hypothesis $\tau<1$ is implicit in the paper's division by $1-\tau$.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 4.1, Theorem 4.1, p. 4

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem unsup_loss_upper_bound :
    ∃ K : ℝ, ∀ {X : Type u} [MeasurableSpace X] {C : Type v} [Countable C] {d : ℕ}
      (D : C → Measure X) (ρ : C → ℝ), IsLatentClassModel D ρ → collisionProb ρ < 1 →
      ∀ (hinge : Bool) (R : ℝ), 0 < R →
      ∀ (F : Set (X → Rep d)), (∀ f ∈ F, IsBoundedRep f R) → IsPointwiseSeparable F →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (fhat : (Fin M → X × X × (Fin 1 → X)) → X → Rep d),
        (∀ S, fhat S ∈ F ∧ ∀ f ∈ F, empUnsupLoss hinge 1 (fhat S) S ≤ empUnsupLoss hinge 1 f S) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
        sampleMeasure D ρ 1 M {S | ¬ ∀ f ∈ F,
            avgMeanSupLoss (stdLoss hinge) D ρ 1 (fhat S) ≤
              1 / (1 - collisionProb ρ) * (unsupLoss hinge D ρ 1 f - collisionProb ρ) +
                1 / (1 - collisionProb ρ) * genError K R 1 M (rademacherAvg F S) δ} ≤
          ENNReal.ofReal δ := by sorry

end ContrastiveUnsupervised
