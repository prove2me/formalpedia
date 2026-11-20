-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finitebarrier_ruinTime_exact_physical_first_size2_mark
-- name    : AvramDividend.Classical.avram_jump6_A_original_finitebarrier_ruinTime_exact_physical_first_size2_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:53:29.816062+00:00
-- url     : https://prove2.me/theorems/d0adb35c-b638-41a0-95da-4eefeb8ea8b9
-- title:
--   Original finite-cap barrier ruinTime equals actual first negative size-two Poisson arrival on a native short Brownian tube
-- statement:
--   For the genuine spectrally negative Lévy path X=B+J, a Brownian tube through σ, physical Poisson path J=0 before σ and Jσ≤−2, and no positive Poisson jumps through σ, imply that the actual admissible finite-cap barrierStrategy with x=1/10,a=1/5 pays no dividends and the controlled risk reserve stays strictly positive for every t<σ, then is strictly negative at σ. The original ruinTime, defined as the infimum of negative reserve clocks, is therefore exactly σ, the physical first marked jump. This fills the original stopped-clock equality obligation in the candidate counterexample to the unit-coefficient fullmark ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finitebarrier_ruinTime_exact_physical_first_size2_mark
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B J : ℝ≥0 → ℝ) (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t + J t)
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hJzero : ∀ t : ℝ≥0, t < σ → J t = 0)
    (hJneg : ∀ t : ℝ≥0, t ≤ σ → J t ≤ 0)
    (hMark : J σ ≤ -2) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
        (σ : ℝ≥0∞) := by sorry
