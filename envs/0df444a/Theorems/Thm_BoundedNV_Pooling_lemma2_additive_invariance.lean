-- Prove2me | Theorems.Thm_BoundedNV_Pooling_lemma2_additive_invariance
-- name    : BoundedNV.Pooling.lemma2_additive_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:06.770959+00:00
-- url     : https://prove2.me/theorems/8fba5d4c-3f2a-411c-af2c-fe10964b150f
-- title:
--   Lemma 2, p. 572 — additive invariance of the choice distribution
-- statement:
--   Let $Y\subseteq\mathbb R$ be a measurable decision domain, and suppose the logit normalizer of a utility $u$ at parameter $\beta>0$ is finite and positive. Adding a constant $a$ to every utility value does not change the choice distribution:
--
--   $$
--   \Psi_{u+a}(y)=\Psi_u(y)\qquad\text{for every }y\in\mathbb R.
--   $$
--
--   This result permits the cost-based logit law used here to represent the paper's profit-based behavioral choice.
--
--   **Formalization Note** The normalizer assumptions make the density a probability density rather than an artifact of Lean's default value for a nonintegrable integral.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 572 (PDF 7), Lemma 2; proof p. 586 (PDF 21), eq. (35)

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Logit

open MeasureTheory

namespace BoundedNV.Pooling

/-- Lemma 2, p. 572: a common additive shift of utility preserves the choice CDF. -/
theorem lemma2_additive_invariance (Y : Set ℝ) (u : ℝ → ℝ) (β a : ℝ)
    (hY : MeasurableSet Y)
    (hu : IntegrableOn (fun v => Real.exp (u v / β)) Y)
    (hZ : 0 < ∫ v in Y, Real.exp (u v / β))
    (hβ : 0 < β) (y : ℝ) :
    logitCDF Y (fun v => u v + a) β y = logitCDF Y u β y := by sorry

end BoundedNV.Pooling
