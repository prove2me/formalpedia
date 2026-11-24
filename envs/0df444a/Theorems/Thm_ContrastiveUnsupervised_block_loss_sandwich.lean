-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_block_loss_sandwich
-- name    : ContrastiveUnsupervised.block_loss_sandwich
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:09:58.367095+00:00
-- url     : https://prove2.me/theorems/76c9f5cb-56d3-4fa8-9af7-52b1f57b88a1
-- title:
--   Proposition 6.2: blocks of similar points give a tighter surrogate
-- statement:
--   Let $\mathcal C$ be a countable set of latent classes with distribution $\rho$, $\tau=\sum_c\rho(c)^2<1$, let $\ell$ be the hinge or logistic loss, let $b\ge1$, and let $f:\mathcal X\to\mathbb R^d$ be measurable and bounded. With the block loss
--
--   $$L^{block}_{un}(f)=\mathbb E\Big[\ell\Big(f(x)^\top\Big(\frac{\sum_if(x_i^+)}{b}-\frac{\sum_if(x_i^-)}{b}\Big)\Big)\Big],$$
--
--   where $x,x_1^+,\dots,x_b^+$ are i.i.d. from $\mathcal D_{c^+}$, $x_1^-,\dots,x_b^-$ are i.i.d. from $\mathcal D_{c^-}$, and $c^+,c^-\sim\rho^2$,
--
--   $$L_{sup}(f)\le\frac{1}{1-\tau}\big(L^{block}_{un}(f)-\tau\big)\le\frac{1}{1-\tau}\big(L_{un}(f)-\tau\big).$$
--
--   Here $L_{sup}$ is the average binary supervised loss and $L_{un}$ uses one negative sample. Averaging over blocks gives a tighter surrogate than single pairs.
--
--   **Formalization Note** The block size $b\ge1$ and $\tau<1$ are implicit in the paper.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 6.3, Proposition 6.2, eq. (12), p. 7; proof in Appendix A.4, p. 13

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem block_loss_sandwich {X : Type*} [MeasurableSpace X] {C : Type*} [Countable C] {d : ℕ}
    (D : C → Measure X) (ρ : C → ℝ) (hDρ : IsLatentClassModel D ρ) (hτ : collisionProb ρ < 1)
    (hinge : Bool) (b : ℕ) (hb : 1 ≤ b) (f : X → Rep d) (R : ℝ) (hf : IsBoundedRep f R) :
    avgSupLoss (stdLoss hinge) D ρ 1 f ≤
        1 / (1 - collisionProb ρ) * (blockUnsupLoss hinge D ρ b f - collisionProb ρ) ∧
      1 / (1 - collisionProb ρ) * (blockUnsupLoss hinge D ρ b f - collisionProb ρ) ≤
        1 / (1 - collisionProb ρ) * (unsupLoss hinge D ρ 1 f - collisionProb ρ) := by sorry

end ContrastiveUnsupervised
