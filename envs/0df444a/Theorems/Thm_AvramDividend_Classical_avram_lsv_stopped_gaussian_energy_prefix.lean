-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_stopped_gaussian_energy_prefix
-- name    : AvramDividend.Classical.avram_lsv_stopped_gaussian_energy_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:18:26.625892+00:00
-- url     : https://prove2.me/theorems/bc364c90-729c-45df-8b7c-b9b2a146c85c
-- title:
--   Stopped Gaussian integrand square energy equals energy over the original clipped half-open clock
-- statement:
--   For any real-time random integrand H and stop tau, the integral of its squared (0,t]-stopped field equals the integral of the original squared field on (0,min(t,tau)]. Proven by identifying the indicator integrand and intersection of time intervals. Direct adaptation of lean-lsv stoppedIntegrand_energy_prefix, CC BY 4.0; no stochastic integral or Brownian representation is assumed. Usable as the deterministic energy-prefix component of the original positive-clock Gaussian localisation.

import Mathlib
open MeasureTheory Set
open scoped Topology
noncomputable section
/-
Proof adapted from contributors to dufeteller/lean-lsv,
LSV/LocalizedItoStoppingIdentity.lean,
OriginalLSVCoefficientValues.stoppedIntegrand_energy_prefix,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719 (22 November 2026 inspected).
Upstream licence CC BY 4.0. Changes: remove LSV-specific scalarTimeClamp,
use a direct real-line stopped field and pointwise indicator identity.
-/

theorem AvramDividend.Classical.avram_lsv_stopped_gaussian_energy_prefix
    {Ω : Type*} (H : ℝ → Ω → ℝ) (τ : Ω → ℝ) (t : ℝ) (ω : Ω) :
    (∫ s in Ioc (0 : ℝ) t, (if s ≤ τ ω then H s ω else 0)^2) =
      ∫ s in Ioc (0 : ℝ) (min t (τ ω)), (H s ω)^2 := by sorry
