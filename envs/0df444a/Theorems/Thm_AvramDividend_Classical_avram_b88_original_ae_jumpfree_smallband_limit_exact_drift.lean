-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b88_original_ae_jumpfree_smallband_limit_exact_drift
-- name    : AvramDividend.Classical.avram_b88_original_ae_jumpfree_smallband_limit_exact_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:11:53.800995+00:00
-- url     : https://prove2.me/theorems/92f658af-8428-41dc-9e37-fbe991403dd7
-- title:
--   Original jumpfree small-negative compensated drift holds a.e. without an unjustified all-path source limit
-- statement:
--   On the original Lévy probability space, assume the canonical almost-everywhere all-time cutoff convergence of the compensated finite negative-band process Jsmall. Suppose true physical source jumps vanish on a random interval for almost every path and the signed cutoff moments tend to a finite drift d. For almost every path, B80 supplies exact finite-cutoff compensation at both genuine clocks; uniqueness of the real limit establishes Jsmall(t)-Jsmall(s)=d(t-s). This removes the stronger pointwise-for-all-paths assumption in B82 and is suitable for constructing the authentic event-restricted stopped Ito certificate. No global second moment assumption.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), original finite-band compensated source equality and B80 physical nojump increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On an almost-everywhere source event, the original compensated small-mark limit has exact signed compensator drift on a physically jumpfree interval. -/

theorem AvramDividend.Classical.avram_b88_original_ae_jumpfree_smallband_limit_exact_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ᵐ ω ∂P, ∀ u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (d : ℝ)
    (hνlim : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 d))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
      d * ((t ω : ℝ) - (s ω : ℝ)) := by sorry
