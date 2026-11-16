-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_claim_3_15
-- name    : BLTCounting.AccuracySpace.Supplement.claim_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:43.633766+00:00
-- url     : https://prove2.me/theorems/16652ad7-5b63-46ff-9734-95bcdc32a4b6
-- title:
--   Claim 3.15 — Positive-semidefinite band domination
-- statement:
--   Fix $\gamma\in(0,1]$ and $\varepsilon\in(0,1)$. For all sufficiently large $m$ and every positive solution of the Section 3 threshold equation, put $\theta_*=h\omega_*$. Then $0<\theta_*\le\pi$, and
--   $$T_h\succeq2(1+\varepsilon)\tau_1B,$$
--   where $B[i,j]=(2\pi)^{-1}\int_{-\theta_*}^{\theta_*}e^{i(i-j)\theta}\,d\theta$. The matrix difference is positive semidefinite. This is the spectral band domination used for Theorem 1.1.
--
--   Differences from the source:
--   - encoding: inherited sufficiently large m regime with 0<θ_*≤π and Loewner domination → eventual quantifier, explicit band bounds in the conclusion and PosSemidef of the difference; reason: the regime and domination are made explicit without new assumptions
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 3.15, printed p. 22 (PDF p. 23)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

open scoped ComplexOrder

namespace BLTCounting.AccuracySpace.Supplement

/-- Claim 3.15, PDF p.23: positive-semidefinite domination, including its inherited band regime. -/
theorem claim_3_15 (γ ε : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ ω : ℝ, IsThreshold m γ ε ω →
        0 < latticeH m γ * ω ∧ latticeH m γ * ω ≤ Real.pi ∧
        (latticeToeplitz m γ -
          (2 * (1 + ε) * tauOne m γ : ℂ) •
            bandMatrix (latticeK m γ) (latticeH m γ * ω)).PosSemidef := by sorry

end BLTCounting.AccuracySpace.Supplement
