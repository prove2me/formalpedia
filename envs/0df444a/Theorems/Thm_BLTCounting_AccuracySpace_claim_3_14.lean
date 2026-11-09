-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_claim_3_14
-- name    : BLTCounting.AccuracySpace.claim_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:35.017181+00:00
-- url     : https://prove2.me/theorems/a4de8acc-2939-45fd-925b-ccfd2d062927
-- title:
--   Trace defect of the band matrix
-- statement:
--   For the $K\times K$ band matrix $B$ with $0<\theta\le\pi$,
--   $$\mathrm{Tr}(B-B^2)=O(\log(K\theta))\qquad(K\theta\to\infty),$$
--   with an implied constant uniform in $K$ and $\theta$. The eigenvalues of $B$ therefore cluster near $0$ and $1$, with only logarithmically many in between.
--
--   Differences from the source:
--   - generalization: the threshold $\theta_*=h\omega_*$ of the respective section → every $\theta$ with $0<\theta\le\pi$; reason: the proof uses only $[-\theta_*,\theta_*]\subseteq[-\pi,\pi]$; the source statement is the special case
--   - reading: $O(\log(K\theta_*))$ with no stated regime → an absolute constant $C$ and a threshold $X_0$, valid for $K\theta\ge X_0$, uniform in $K$ and $\theta$; reason: $\log(K\theta)$ is not positive for small $K\theta$; the source applies the bound as $K\theta_*\to\infty$
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 3.14, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Matrix

namespace BLTCounting.AccuracySpace

/-- Claim 3.14, PDF p. 22: `Tr(B - B²) = O(log(Kθ))` as `Kθ → ∞`, with a constant uniform in `K` and
`θ ∈ (0, π]`. -/
theorem claim_3_14 :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ (K : ℕ) (θ : ℝ), 0 < θ → θ ≤ Real.pi → X₀ ≤ (K : ℝ) * θ →
      ‖(bandMatrix K θ - bandMatrix K θ * bandMatrix K θ).trace‖ ≤
        C * Real.log ((K : ℝ) * θ) := by sorry

end BLTCounting.AccuracySpace
