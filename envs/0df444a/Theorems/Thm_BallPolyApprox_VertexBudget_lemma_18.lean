-- Prove2me | Theorems.Thm_BallPolyApprox_VertexBudget_lemma_18
-- name    : BallPolyApprox.VertexBudget.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:56:34.456177+00:00
-- url     : https://prove2.me/theorems/a35a783d-f7f0-4dda-bb81-90c52b16b30e
-- title:
--   Lemma 18 — sub-Gaussian lower tail of $(d-1)Q_d$
-- statement:
--   There exist absolute constants $C,c>0$ such that for every $d\ge2$ the angular variable $Q_d$ of Lemma 16 satisfies
--   $$\mathbb P\big((d-1)Q_d\le2-s\big)\le Ce^{-c(d-1)s^2},\qquad0<s<2.$$
--
--   Differences from the source:
--   - generalization: §5.3.1 standing assumption: d sufficiently large → every d ≥ 2; reason: for d below the source's threshold d_0 the probability is at most 1 ≤ C' e^{−4c(d_0 − 1)} ≤ C' e^{−c(d−1)s²} with C' = max(C, e^{4c d_0}), so the statement for all d ≥ 2 follows from the source's and specializes to it
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), Lemma 18, p. 18 (PDF 20)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer
import Definitions.Def_BallPolyApprox_VertexBudget_AngularLaw

set_option autoImplicit false

open MeasureTheory

namespace BallPolyApprox.VertexBudget

/-- Lemma 18 (p. 18, PDF 20): there are absolute constants `C, c > 0` such that the angular
variable `Q_d` satisfies `P((d − 1) Q_d ≤ 2 − s) ≤ C e^{−c(d−1)s²}` for `0 < s < 2`; stated for
every `d ≥ 2`. -/
theorem lemma_18 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ s : ℝ, 0 < s → s < 2 →
      (QLaw d).real {q : ℝ | ((d : ℝ) - 1) * q ≤ 2 - s} ≤
        C * Real.exp (-(c * ((d : ℝ) - 1) * s ^ 2)) := by sorry

end BallPolyApprox.VertexBudget
