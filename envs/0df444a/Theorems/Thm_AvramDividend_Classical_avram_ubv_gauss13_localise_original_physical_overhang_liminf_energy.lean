-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_physical_overhang_liminf_energy
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_overhang_liminf_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:56:48.57346+00:00
-- url     : https://prove2.me/theorems/135fcca1-046b-4781-827b-5934298d4933
-- title:
--   Original Gaussian physical stop-straddling quadratic energy Fatou passage
-- statement:
--   For actual original X.X centred source values along sampled future stopping clocks converging almost surely to the physical stopping clock, Fatou transfers the quadratic energy of the final stop-straddling overhang from finite sampled approximants to the true physical clock. Requires source-exact a.e. path convergence and measurability of approximant squares. This is valid without assuming uniform integrability, Gaussian fourth moments or an auxiliary Brownian process; a common sampled-grid and time-gap construction must supply the approximant energy bound from Proved 9954ba8b.
-- source:
--   Mathlib nonnegative Fatou on original stopped centred source; preexisting original-path ceiling convergence 23b87d40 and original Gaussian stop energy 9954ba8b are intended consumer inputs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_overhang_liminf_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0)
    (s : ℕ → Ω → ℝ≥0)
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (s n ω) ω -
        (s n ω : ℝ) * X.c) atTop
        (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)))
    (hMeas : ∀ n, Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
          (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2))) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2) ∂P) ≤
      Filter.liminf (fun n =>
        ∫⁻ ω, ENNReal.ofReal
          (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
            (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P)
      atTop := by sorry
