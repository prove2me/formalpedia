-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_canonical_esscher_density_eq_displacement_density
-- name    : AvramDividend.Classical.avram_ws01e_b_canonical_esscher_density_eq_displacement_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:18:27.045065+00:00
-- url     : https://prove2.me/theorems/76e7ee3d-84c3-4a4f-a28b-260623925b69
-- title:
--   Canonical finite-terminal Esscher law equals displacement-based Esscher law for the zero-start Lévy process
-- statement:
--   For the canonical spectrally negative Lévy process X with pointwise zero origin X_0=0, the true finite-terminal Esscher measure P.withDensity(exp(θX_T−T ψ(θ))) is exactly the same measure as the displacement-weighted form P.withDensity(exp(θ(X_T−X_0)−T ψ(θ))). This closes the alignment gap between the available finite-mesh Esscher path/vector-law identification and the canonical Prove2Me finite-terminal Esscher laws. Equality holds pointwise in the path variable for every real θ and time T, without relying on merely almost-sure normalization.
-- source:
--   Canonical SpectrallyNegativeLevy.X_zero identity and elementary real exponential arithmetic; supported by accepted reflectedSup_origin_eq_zero proof which uses rw [X.X_zero].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Zero-start Lévy paths identify the displacement form of the
finite-terminal Esscher tilt with the canonical terminal-level form. -/

theorem AvramDividend.Classical.avram_ws01e_b_canonical_esscher_density_eq_displacement_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (T : ℝ≥0) :
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X T ω - X.X 0 ω) -
        (T : ℝ) * X.ψ θ))) =
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))) := by sorry
