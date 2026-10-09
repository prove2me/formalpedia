-- Prove2me | Theorems.Thm_BanditCovariates_SE_phi_bound
-- name    : BanditCovariates.SE.phi_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:22.300129+00:00
-- url     : https://prove2.me/theorems/13c56d33-1010-4546-8691-7f536b0b7443
-- title:
--   §2, p. 8 — best-arm elimination probability Φ_j(τ)
-- statement:
--   For a suboptimal arm $j$, let $\widehat\Delta_j(s)$ be its empirical gap against the best arm. With $\gamma\ge1$, integer $T\ge1$, and $\tau\ge1$, define $\Phi_j(\tau)$ as the probability that $\widehat\Delta_j(s)\le-\gamma U(s,T)$ for at least one $s\le\tau$. Then
--
--   $$\Phi_j(\tau)\le\frac{4\tau}{T}.$$
--
--   This estimate controls the chance that the best arm is eliminated by a suboptimal arm at any of the early rounds. The bound concerns the reward stack's empirical means, whether or not both arms are still active at that time.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 8, display after (2.6) (Φ_j(τ) ≤ 4τ/T)

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

namespace BanditCovariates.SE

open MeasureTheory ProbabilityTheory

/-- The display after (2.6), p. 8: Φ_j(τ) ≤ 4τ/T. -/
theorem phi_bound {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (K : ℕ) (hK : 1 ≤ K)
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (f : Fin (K + 1) → ℝ)
    (hmodel : RegretBandits.Stochastic.IsStochasticBandit P Y f)
    (hbounded : ∀ i k, ∀ᵐ ω ∂P, Y i k ω ∈ Set.Icc (0 : ℝ) 1)
    (hordered : Monotone f)
    (hbest : ∀ i, i ≠ Fin.last K → f i < f (Fin.last K))
    (j : Fin (K + 1)) (hj : j ≠ Fin.last K)
    (T τ : ℕ) (hT : 1 ≤ T) (hτ : 1 ≤ τ) (γ : ℝ) (hγ : 1 ≤ γ) :
    P.real {ω | ∃ s ∈ Finset.Icc 1 τ,
      estimatedGap Y j s ω ≤ -γ * U s T} ≤
      4 * (τ : ℝ) / (T : ℝ) := by sorry

end BanditCovariates.SE
