-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_subgaussian_neq_loss_le_margin_loss
-- name    : ContrastiveUnsupervised.subgaussian_neq_loss_le_margin_loss
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:08:42.560933+00:00
-- url     : https://prove2.me/theorems/30c9c6b1-5cab-4240-8924-dcb0cec6038c
-- title:
--   Lemma 5.1 (as proved): sub-Gaussian representations
-- statement:
--   Let $\mathcal C$ be a countable set of latent classes with distribution $\rho$, let $\tau=\sum_c\rho(c)^2<1$, and let $\ell$ be the hinge loss. Let $f:\mathcal X\to\mathbb R^d$ be measurable with $\|f(x)\|\le R$ for all $x$. Suppose that, for every class $c$, $f(X)$ with $X\sim\mathcal D_c$ is $\sigma^2$-sub-Gaussian in every direction, where $\sigma\ge0$. Then for every $\varepsilon>0$,
--
--   $$L^{\ne}_{un}(f)\le\gamma\,L^\mu_{\gamma,sup}(f)+\varepsilon,$$
--
--   where $L^\mu_{\gamma,sup}$ is the average binary mean-classifier loss with $\ell_\gamma(x)=(1-x/\gamma)_+$. Here
--
--   $$\gamma=1+2R\sigma\sqrt{2\log R+\log(3/\varepsilon)}\ \text{ if }R\ge1,\qquad\gamma=1+2R\sigma\sqrt{\log(3/\varepsilon)}\ \text{ if }R<1.$$
--
--   **Formalization Note** The paper prints $\gamma=1+c'R\sigma\sqrt{\log(R/\varepsilon)}$ with an unspecified constant. That expression is undefined for $\varepsilon\ge R$, and the proof (Appendix A.2 and its footnote) establishes the explicit $\gamma$ above, which is stated here. Lean's square root of a negative number is $0$; then $\gamma=1$ and the inequality still holds. The lemma is stated for the hinge loss, which is the loss the proof uses; for the logistic loss it fails. $R$ is any bound on $\|f\|$; the right side increases with $R$, so this is equivalent to taking $R=\max_x\|f(x)\|$.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 5.2, Lemma 5.1, p. 6; proof in Appendix A.2, p. 11

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem subgaussian_neq_loss_le_margin_loss {X : Type*} [MeasurableSpace X] {C : Type*}
    [Countable C] {d : ℕ} (D : C → Measure X) (ρ : C → ℝ) (hDρ : IsLatentClassModel D ρ)
    (hτ : collisionProb ρ < 1) (f : X → Rep d) (R σ : ℝ) (hf : IsBoundedRep f R)
    (hσ : 0 ≤ σ) (hsub : IsSubGaussianRep D f σ) (ε : ℝ) (hε : 0 < ε) :
    unsupLossNeq true D ρ 1 f ≤
      subGaussianMargin R σ ε *
          avgMeanSupLoss (marginHingeLoss (subGaussianMargin R σ ε)) D ρ 1 f + ε := by sorry

end ContrastiveUnsupervised
