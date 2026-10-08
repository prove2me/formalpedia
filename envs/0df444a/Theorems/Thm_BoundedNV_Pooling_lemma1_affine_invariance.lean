-- Prove2me | Theorems.Thm_BoundedNV_Pooling_lemma1_affine_invariance
-- name    : BoundedNV.Pooling.lemma1_affine_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:56.993999+00:00
-- url     : https://prove2.me/theorems/696ee67d-e764-4f8a-8d2d-306cc9795966
-- title:
--   Lemma 1, p. 572 — affine invariance of the choice distribution
-- statement:
--   Let $Y\subseteq\mathbb R$ be a measurable decision domain, and let its logit normalizer for utility $u$ and parameter $\beta>0$ be finite and positive. For a positive scale $a$ and a shift $d$, transform each choice by $\widetilde y=ay+d$ and transport the utility by $\widetilde u(z)=u((z-d)/a)$. Then, for every $y$,
--
--   $$
--   \widetilde\Psi(ay+d)=\Psi(y).
--   $$
--
--   The lemma identifies changes of units and origin that leave the choice law unchanged. It supports the standardization of Gaussian orders in Proposition 7.
--
--   **Formalization Note** The paper leaves the sign of $a$ unstated. A negative scale reverses the CDF order, so this statement requires $a>0$. The finite positive normalizer makes both sides actual choice distributions. The shift is named $d$ to distinguish it from §9's backlog cost $b$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 572 (PDF 7), Lemma 1; proof p. 586 (PDF 21), eqs. (33)–(34)

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Logit

open MeasureTheory

namespace BoundedNV.Pooling

/-- Lemma 1, p. 572: order-preserving affine changes of the choice domain preserve its CDF. -/
theorem lemma1_affine_invariance (Y : Set ℝ) (u : ℝ → ℝ) (β a d : ℝ)
    (hY : MeasurableSet Y)
    (hu : IntegrableOn (fun v => Real.exp (u v / β)) Y)
    (hZ : 0 < ∫ v in Y, Real.exp (u v / β))
    (hβ : 0 < β) (ha : 0 < a) (y : ℝ) :
    logitCDF ((fun v : ℝ => a * v + d) '' Y)
        (fun z => u ((z - d) / a)) β (a * y + d) =
      logitCDF Y u β y := by sorry

end BoundedNV.Pooling
