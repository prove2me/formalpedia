-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_k_negative_samples_guarantee
-- name    : ContrastiveUnsupervised.k_negative_samples_guarantee
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:10:35.792673+00:00
-- url     : https://prove2.me/theorems/213c6a69-72eb-4873-aaf5-adc4e7fff4b1
-- title:
--   Theorem B.1: guarantee with k negative samples
-- statement:
--   Let $\mathcal C$ be a countable set of latent classes with distribution $\rho$ and class distributions $\mathcal D_c$. Let $k\ge1$ be the number of negative samples, with $\tau_k=P[I^+\ne\emptyset]<1$. Let every task $\mathcal T$ have a label distribution $\mathcal D_{\mathcal T}$. Let $\ell$ be the hinge or logistic loss, and let $\mathcal F$ be a pointwise separable class of measurable $f$ with $\|f(\cdot)\|\le R$, $R>0$. Let $\widehat f(\mathcal S)\in\operatorname{argmin}_{f\in\mathcal F}\widehat L_{un}(f)$ for training sets of $M\ge1$ tuples $(x,x^+,x_1^-,\dots,x_k^-)$ drawn from $(\mathcal D_{sim}\times\mathcal D_{neg}^k)^M$. There are absolute constants $K$ and $c'>0$ such that, for every $0<\delta\le1/2$, with probability at least $1-\delta$, for all $f\in\mathcal F$,
--
--   $$\mathbb E_{\mathcal T\sim\mathcal D}\Big[\frac{\rho^+_{min}(\mathcal T)}{p_{max}(\mathcal T)}L^\mu_{sup}(\mathcal T,\widehat f)\Big]\le\frac{1-\tau'}{1-\tau_k}L^{\ne}_{un}(f)+c'k\frac{\tau_1}{1-\tau_k}s(f)+\frac{1}{1-\tau_k}Gen_M,$$
--
--   with $Gen_M=K\big(R\sqrt k\,\mathcal R_{\mathcal S}(\mathcal F)/M+(R^2+\log k)\sqrt{\log(1/\delta)/M}\big)$, $\tau_1=\sum_c\rho(c)^2$, $\tau'=P[c_i^-=c^+\ \forall i]$, and $\mathcal D$ the law of the set of distinct classes of $(c^+,c_1^-,\dots,c_k^-)\sim\rho^{k+1}$ conditioned on $c^+\notin\{c_i^-\}$.
--
--   This is the formal version of Theorem 6.1. For $k=1$ and uniform $\mathcal D_{\mathcal T}$ it gives the second inequality of Theorem 4.5 (then $\rho^+_{min}/p_{max}=1$ and $\tau'=\tau_k=\tau$); it does not give the first inequality $L_{sup}\le L^\mu_{sup}$, and for non-uniform $\mathcal D_{\mathcal T}$ it bounds a different, weighted quantity.
--
--   **Formalization Note** The paper's $O(\cdot)$ is an absolute constant $K$, and "with probability at least $1-\delta$" means that the outer measure of the failure set is at most $\delta$. The statement is restricted to $\delta\le1/2$ because the proof (Mohri et al., Theorem 3.1, and Hoeffding) produces $\log(4/\delta)$ and $\log(2/\delta)$. These are $O(\log(1/\delta))$ only for $\delta$ bounded away from $1$; for $\delta\le1/2$ the two forms agree up to the constant. Pointwise separability of $\mathcal F$ and measurability of each $f$ are standing conventions the paper does not state. The hypothesis $\tau_k<1$ is implicit in the paper's division by $1-\tau_k$. Losses of an empty vector are $0$, the convention the proof uses for $L^{\ne}_{un}$ when $|I^+|=k$.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Appendix B.1, Theorem B.1, p. 14, proof pp. 14-16 (formal version of Section 6.1, Theorem 6.1)

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem k_negative_samples_guarantee :
    ∃ K c' : ℝ, 0 < c' ∧
      ∀ {X : Type u} [MeasurableSpace X] {C : Type v} [Countable C] {d : ℕ}
      (D : C → Measure X) (ρ : C → ℝ), IsLatentClassModel D ρ →
      ∀ (k : ℕ), 1 ≤ k → tauK ρ k < 1 →
      ∀ (pT : Finset C → C → ℝ), IsTaskDistFamily pT →
      ∀ (hinge : Bool) (R : ℝ), 0 < R →
      ∀ (F : Set (X → Rep d)), (∀ f ∈ F, IsBoundedRep f R) → IsPointwiseSeparable F →
      ∀ (M : ℕ), 1 ≤ M →
      ∀ (fhat : (Fin M → X × X × (Fin k → X)) → X → Rep d),
        (∀ S, fhat S ∈ F ∧ ∀ f ∈ F, empUnsupLoss hinge k (fhat S) S ≤ empUnsupLoss hinge k f S) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
        sampleMeasure D ρ k M {S | ¬ ∀ f ∈ F,
            weightedTaskMeanSupLoss (stdLoss hinge) D ρ k pT (fhat S) ≤
              (1 - tauAll ρ k) / (1 - tauK ρ k) * unsupLossNeq hinge D ρ k f +
                c' * k * (collisionProb ρ / (1 - tauK ρ k)) * intraclassDeviation D ρ f +
                1 / (1 - tauK ρ k) * genError K R k M (rademacherAvg F S) δ} ≤
          ENNReal.ofReal δ := by sorry

end ContrastiveUnsupervised
