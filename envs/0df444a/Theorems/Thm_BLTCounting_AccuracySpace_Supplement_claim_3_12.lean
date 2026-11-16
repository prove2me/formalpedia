-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_claim_3_12
-- name    : BLTCounting.AccuracySpace.Supplement.claim_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:03.486195+00:00
-- url     : https://prove2.me/theorems/9c0002a3-fa97-474e-b162-1eba2a0598c2
-- title:
--   Claim 3.12 — Toeplitz symbol lower bound on the full band
-- statement:
--   Fix $\gamma\in(0,1]$ and $\varepsilon\in(0,1)$. For all sufficiently large $m$ and the positive threshold solution, put $\theta_*=h\omega_*$. The Toeplitz symbol is real on the band, and
--   $$\widehat a_h(\theta)\ge2(1+\varepsilon)\tau_1\qquad(-\theta_*\le\theta\le\theta_*).$$
--   This supplies the full band lower bound for the Section 3 unscaled Toeplitz matrix.
--
--   Differences from the source:
--   - encoding: real-valued symbol inequality on the threshold band → zero imaginary part and the inequality for the real part, eventually in m; reason: the published symbol is complex-valued and its realness is proved as a conclusion
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 3.12, printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Claim 3.12, PDF p.21. Realness of the symbol is included, since its definition is complex. -/
theorem claim_3_12 (γ ε : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ ω : ℝ, IsThreshold m γ ε ω →
      ∀ θ : ℝ, θ ∈ Set.Icc (-(latticeH m γ * ω)) (latticeH m γ * ω) →
        (sampledSymbol (latticeH m γ) θ).im = 0 ∧
        2 * (1 + ε) * tauOne m γ ≤ (sampledSymbol (latticeH m γ) θ).re := by sorry

end BLTCounting.AccuracySpace.Supplement
