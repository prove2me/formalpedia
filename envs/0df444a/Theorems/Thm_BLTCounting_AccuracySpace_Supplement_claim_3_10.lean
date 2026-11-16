-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_claim_3_10
-- name    : BLTCounting.AccuracySpace.Supplement.claim_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:58.687221+00:00
-- url     : https://prove2.me/theorems/11adcae5-00f8-4aef-8d82-bb31d6263333
-- title:
--   Claim 3.10 — Existence and uniqueness of the Fourier threshold
-- statement:
--   Fix $\gamma\in(0,1]$ and $\varepsilon>0$. For all sufficiently large integers $m$, depending only on these fixed parameters, there exists a unique $\omega_*>0$ satisfying
--   $$\widehat c_0(\omega_*)=2(1+\varepsilon)\tau_1h,\qquad \tau_1=m^{1-\gamma}.$$
--   The lattice step $h$ is the Section 3 step. Existence and uniqueness are conclusions rather than assumed data.
--
--   Differences from the source:
--   - encoding: for all sufficiently large m → one natural threshold m₀ depending on γ,ε; reason: explicit asymptotic quantifiers change no instance
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 3.10, printed p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Claim 3.10, PDF p.20; existence is part of the conclusion. -/
theorem claim_3_10 (γ ε : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃! ω : ℝ, IsThreshold m γ ε ω := by sorry

end BLTCounting.AccuracySpace.Supplement
