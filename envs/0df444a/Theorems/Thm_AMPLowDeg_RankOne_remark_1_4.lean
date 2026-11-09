-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_remark_1_4
-- name    : AMPLowDeg.RankOne.remark_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:25.892158+00:00
-- url     : https://prove2.me/theorems/e32b565f-1446-4e18-91fb-f846aed6bc5e
-- title:
--   Remark 1.4, eq. (1.8) — moment-dependent lower bound
-- statement:
--   Let $\pi$ be a prior with nonzero mean and all moments finite, and put $M_D=\max\{1,\|\Theta\|_{4D+2}\}$. For all integers $n\ge1$ and $D\ge1$,
--
--   $$
--   \mathrm{MMSE}_{\le D}\ \ge\ m_2-q_{\mathrm{AMP}}-\sum_{g=1}^{D}\left(\frac{2^{54}(D+1)^{48}M_D^{16}}{n}\right)^{g}.
--   $$
--
--   This is the precise form of the main theorem for priors that need not be sub-Gaussian; Theorem 1.2 follows from it through $M_D\le2K\sqrt{D+1}$.
--
--   Differences from the source:
--
--   - encoding: MMSE_{≤D} ≥ x with MMSE_{≤D} a real infimum → ENNReal.ofReal x ≤ mmseLD π n D, the risk being a lower Lebesgue integral in [0, ∞]; reason: MMSE_{≤D} is finite (the zero estimator has risk m₂), so for a finite value both forms say the same; no integrability convention is involved
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 5, Remark 1.4, eq. (1.8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Remark 1.4, eq. (1.8), p. 5 — the moment-dependent bound: for a prior with nonzero mean and all
moments finite, `M_D = max{1, ‖Θ‖_{4D+2}}`, and all `n, D ≥ 1`,
`MMSE_{≤D} ≥ m₂ − q_AMP − Σ_{g=1}^{D} (2^{54}(D+1)^{48} M_D^{16} / n)^g`. -/
theorem remark_1_4 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n D : ℕ) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    ENNReal.ofReal (m2 π - qAMP π -
        ∑ g ∈ Finset.Icc 1 D, ((2 : ℝ) ^ 54 * ((D : ℝ) + 1) ^ 48 * MD π D ^ 16 / n) ^ g) ≤
      mmseLD π n D := by sorry

end AMPLowDeg.RankOne
