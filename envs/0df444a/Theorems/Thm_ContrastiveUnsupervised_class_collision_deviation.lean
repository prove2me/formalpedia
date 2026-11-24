-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_class_collision_deviation
-- name    : ContrastiveUnsupervised.class_collision_deviation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:06:07.727802+00:00
-- url     : https://prove2.me/theorems/bf2fafd7-850a-4aa7-bee9-167355f377ac
-- title:
--   Lemma A.1: class collision lemma
-- statement:
--   There is an absolute constant $c'>0$ with the following property. Let $\mathcal D_c$ be a probability distribution on $\mathcal X$, let $f:\mathcal X\to\mathbb R^d$ be measurable and bounded, let $t\ge1$, and let $\ell:\mathbb R^t\to\mathbb R$ be the $t$-way hinge or logistic loss. For $x,x^+,x_1^-,\dots,x_t^-$ i.i.d. from $\mathcal D_c$, let
--
--   $$L^=_{un,c}(f)=\mathbb E\,\ell\big(\{f(x)^\top(f(x^+)-f(x_i^-))\}_{i=1}^t\big).$$
--
--   Then
--
--   $$L^=_{un,c}(f)-\ell(\vec0)\le c'\,t\,\sqrt{\|\Sigma(f,c)\|_2}\;\mathbb E_{x\sim\mathcal D_c}\|f(x)\|,$$
--
--   where $\Sigma(f,c)$ is the covariance matrix of $f(x)$, $x\sim\mathcal D_c$.
--
--   When the negative samples come from the same class as the positive pair, the excess over $\ell(\vec0)$ is controlled by the spread of $f$ within the class.
--
--   **Formalization Note** "$c'$ is a positive constant" is read as one constant valid for every $\mathcal X$, $\mathcal D_c$, $f$, $t$ and both losses.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Appendix A.1, Lemma A.1, eq. (13), p. 11

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem class_collision_deviation :
    ∃ c' : ℝ, 0 < c' ∧
      ∀ {X : Type u} [MeasurableSpace X] {C : Type v} {d : ℕ} (D : C → Measure X),
        (∀ c, IsProbabilityMeasure (D c)) →
        ∀ (hinge : Bool) (f : X → Rep d) (R : ℝ), IsBoundedRep f R →
        ∀ (t : ℕ), 1 ≤ t → ∀ c : C,
          condUnsupLoss hinge D t f c (fun _ => c) Finset.univ -
              stdLoss hinge (Finset.univ : Finset (Fin t)) (fun _ => (0 : ℝ)) ≤
            c' * t * (Real.sqrt (specNorm (classCov D f c)) * ∫ x, ‖f x‖ ∂(D c)) := by sorry

end ContrastiveUnsupervised
