-- Prove2me | Theorems.Thm_ContrastiveUnsupervised_same_class_loss_le_deviation
-- name    : ContrastiveUnsupervised.same_class_loss_le_deviation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:06:51.044284+00:00
-- url     : https://prove2.me/theorems/2c806c7e-8257-4fd0-8749-181dc57a47c5
-- title:
--   Lemma 4.4: the same-class loss is controlled by the intraclass deviation
-- statement:
--   There is an absolute constant $c'>0$ such that for every latent class model ($\rho$ a distribution on a countable set of classes, $\mathcal D_c$ the class distributions), either loss (hinge or logistic), and every measurable bounded $f:\mathcal X\to\mathbb R^d$,
--
--   $$L^=_{un}(f)-1\le c'\,s(f).$$
--
--   Here $L^=_{un}(f)=\mathbb E_{c\sim\nu,\ x,x^+,x^-\sim\mathcal D_c^3}\,\ell(f(x)^\top(f(x^+)-f(x^-)))$ with $\nu(c)\propto\rho(c)^2$, and $s(f)=\mathbb E_{c\sim\nu}\big[\sqrt{\|\Sigma(f,c)\|_2}\,\mathbb E_{x\sim\mathcal D_c}\|f(x)\|\big]$ is the intraclass deviation.
--
--   **Formalization Note** The constant $c'$ is universal, as in the paper's use of the lemma in Theorem 4.5.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 4.2, Lemma 4.4, eq. (9), p. 5; proof in Appendix A.1, p. 11

import Mathlib
import Definitions.Def_ContrastiveUnsupervised_Basic

open MeasureTheory Filter Topology

universe u v

namespace ContrastiveUnsupervised

theorem same_class_loss_le_deviation :
    ∃ c' : ℝ, 0 < c' ∧
      ∀ {X : Type u} [MeasurableSpace X] {C : Type v} [Countable C] {d : ℕ}
        (D : C → Measure X) (ρ : C → ℝ), IsLatentClassModel D ρ →
        ∀ (hinge : Bool) (f : X → Rep d) (R : ℝ), IsBoundedRep f R →
          unsupLossEq hinge D ρ f - 1 ≤ c' * intraclassDeviation D ρ f := by sorry

end ContrastiveUnsupervised
