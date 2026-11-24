-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_competitive_bound_subgaussian
-- name    : ContrastiveUnsupervised.competitive_bound_subgaussian
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:09:17.524158+00:00
-- url     : https://prove2.me/theorems/15cb4e3d-9d89-4621-a114-42ea775a08ea
-- title:
--   Corollary 5.1.1 (as proved): competitive bound via intraclass concentration
-- statement:
--   Let the setting of Theorem 4.5 hold with the hinge loss: a countable set of classes with $\tau<1$, a pointwise separable class $\mathcal F$ of measurable representations with $\|f\|\le R$, and an empirical minimizer $\widehat f$ on $M\ge1$ tuples. There are absolute constants $K$ and $c'>0$ such that, for every $\varepsilon>0$ and $0<\delta\le1/2$, with probability at least $1-\delta$ over the training set, the following holds for every $f\in\mathcal F$ such that $f(X)$, $X\sim\mathcal D_c$, is $\sigma^2$-sub-Gaussian in every direction for every class $c$ and $\|f(\cdot)\|\le R_f$:
--
--   $$L^\mu_{sup}(\widehat f)\le\gamma(f)\,L^\mu_{\gamma(f),sup}(f)+\beta\,s(f)+\eta\,Gen_M+\varepsilon.$$
--
--   Here $\gamma(f)$ is the margin of Lemma 5.1 for $R_f,\sigma,\varepsilon$, $\beta=c'\frac{\tau}{1-\tau}$, $\eta=\frac{1}{1-\tau}$, and $Gen_M=K\big(R\,\mathcal R_{\mathcal S}(\mathcal F)/M+R^2\sqrt{\log(1/\delta)/M}\big)$.
--
--   **Formalization Note** The paper prints $\eta=\frac{\tau}{1-\tau}$. Combining Lemma 5.1 with Theorem 4.5, as the paper does, gives $\eta=\frac1{1-\tau}$, and the printed value is false (REPORT.md gives a counterexample). The sub-Gaussian hypothesis on $f$, which the printed corollary leaves implicit in "$\gamma(f)$ as defined in Lemma 5.1", is stated explicitly. The paper's $O(\cdot)$ is an absolute constant $K$, and "with probability at least $1-\delta$" means that the outer measure of the failure set is at most $\delta$. The statement is restricted to $\delta\le1/2$ because the proof (Mohri et al., Theorem 3.1, and Hoeffding) produces $\log(4/\delta)$ and $\log(2/\delta)$. These are $O(\log(1/\delta))$ only for $\delta$ bounded away from $1$; for $\delta\le1/2$ the two forms agree up to the constant. Pointwise separability of $\mathcal F$ and measurability of each $f$ are standing conventions the paper does not state. The hypothesis $\tau<1$ is implicit in the paper's division by $1-\tau$.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 5.2, Corollary 5.1.1, p. 6

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem competitive_bound_subgaussian :
    ∃ K c' : ℝ, 0 < c' ∧
      ∀ {X : Type u} [MeasurableSpace X] {C : Type v} [Countable C] {d : ℕ}
      (D : C → Measure X) (ρ : C → ℝ), IsLatentClassModel D ρ → collisionProb ρ < 1 →
      ∀ (R : ℝ), 0 < R →
      ∀ (F : Set (X → Rep d)), (∀ f ∈ F, IsBoundedRep f R) → IsPointwiseSeparable F →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (fhat : (Fin M → X × X × (Fin 1 → X)) → X → Rep d),
        (∀ S, fhat S ∈ F ∧ ∀ f ∈ F, empUnsupLoss true 1 (fhat S) S ≤ empUnsupLoss true 1 f S) →
      ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
        sampleMeasure D ρ 1 M {S | ¬ ∀ f ∈ F, ∀ (σ Rf : ℝ), 0 ≤ σ → IsSubGaussianRep D f σ →
            (∀ x, ‖f x‖ ≤ Rf) →
            avgMeanSupLoss (stdLoss true) D ρ 1 (fhat S) ≤
              subGaussianMargin Rf σ ε *
                  avgMeanSupLoss (marginHingeLoss (subGaussianMargin Rf σ ε)) D ρ 1 f +
                c' * (collisionProb ρ / (1 - collisionProb ρ)) * intraclassDeviation D ρ f +
                1 / (1 - collisionProb ρ) * genError K R 1 M (rademacherAvg F S) δ + ε} ≤
          ENNReal.ofReal δ := by sorry

end ContrastiveUnsupervised
