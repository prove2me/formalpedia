-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_mean_classifier_loss_le_unsup_loss
-- name    : ContrastiveUnsupervised.mean_classifier_loss_le_unsup_loss
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:05:21.397099+00:00
-- url     : https://prove2.me/theorems/2d7de1ef-398f-4c41-8652-a3979d5479c2
-- title:
--   Lemma 4.3: the unsupervised loss bounds the mean classifier loss
-- statement:
--   Let $\mathcal C$ be a countable set of latent classes with distribution $\rho$, let each class $c$ have a data distribution $\mathcal D_c$, and let $\tau=\sum_c\rho(c)^2<1$ be the probability that two independent classes coincide. Let $\ell$ be the hinge or the logistic loss, and let $f:\mathcal X\to\mathbb R^d$ be measurable and bounded. Then, for binary tasks with uniform label distribution and one negative sample,
--
--   $$L^\mu_{sup}(f)\le\frac{1}{1-\tau}\big(L_{un}(f)-\tau\big).$$
--
--   The contrastive loss is therefore a surrogate for the average loss of the mean classifier.
--
--   **Formalization Note** The paper states the lemma for $f\in\mathcal F$, which only gives boundedness and measurability. Those are the hypotheses here. The hypothesis $\tau<1$ is implicit in the paper.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 4.1, Lemma 4.3, p. 4

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem mean_classifier_loss_le_unsup_loss {X : Type*} [MeasurableSpace X] {C : Type*}
    [Countable C] {d : ℕ} (D : C → Measure X) (ρ : C → ℝ) (hDρ : IsLatentClassModel D ρ)
    (hτ : collisionProb ρ < 1) (hinge : Bool) (f : X → Rep d) (R : ℝ) (hf : IsBoundedRep f R) :
    avgMeanSupLoss (stdLoss hinge) D ρ 1 f ≤
      (unsupLoss hinge D ρ 1 f - collisionProb ρ) / (1 - collisionProb ρ) := by sorry

end ContrastiveUnsupervised
