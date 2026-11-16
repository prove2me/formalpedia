-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_claim_3_11
-- name    : BLTCounting.AccuracySpace.Supplement.claim_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:24.509915+00:00
-- url     : https://prove2.me/theorems/b8fcd3d9-bc22-435d-968a-204fa256930a
-- title:
--   Claim 3.11 — Sharp Fourier threshold asymptotics
-- statement:
--   Fix $\gamma\in(0,1]$ and $\varepsilon>0$. For the positive solution of $\widehat c_0(\omega_*)=2(1+\varepsilon)\tau_1h$, with $L=\log m$, as $m\to\infty$,
--   $$\omega_*={\gamma\over2\pi}L-{3\over2\pi}\log L+O(1)=\left({\gamma\over2\pi}-o(1)\right)L.$$
--   The bounded remainder and all sufficiently large thresholds depend only on $\gamma,\varepsilon$ and are uniform over the solutions. The second equality is stated as convergence of $\omega_*/L$ to $\gamma/(2\pi)$.
--
--   Differences from the source:
--   - encoding: O(1) and (γ/(2π)−o(1))L → a uniform absolute remainder bound and an explicit limit of ω/L; reason: these are the defining asymptotic meanings with γ,ε fixed
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Claim 3.11, printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Claim 3.11, PDF p.21. Both the logarithmic correction and leading asymptotic are retained.
The statements are uniform over every solution of the actual threshold equation. -/
theorem claim_3_11 (γ ε : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) :
    (∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ ω : ℝ, IsThreshold m γ ε ω →
        |ω - (γ / (2 * Real.pi) * latticeL m -
          3 / (2 * Real.pi) * Real.log (latticeL m))| ≤ C) ∧
    (∀ δ : ℝ, 0 < δ → ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ ω : ℝ, IsThreshold m γ ε ω →
        |ω / latticeL m - γ / (2 * Real.pi)| ≤ δ) := by sorry

end BLTCounting.AccuracySpace.Supplement
