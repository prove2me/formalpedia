-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_common_ceiling_pair_sampled_energy
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_common_ceiling_pair_sampled_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:47:21.562062+00:00
-- url     : https://prove2.me/theorems/ccfe93ed-5f1f-45d6-81a3-b7b961ba274b
-- title:
--   Original Gaussian common ceiling pair nonnegative sampled energy bound
-- statement:
--   Given two true sampled ceilings of bounded original physical stopping clocks in the same original right-continuous sampled filtration, use their minimum and maximum stopping indices and Proved genuine Gaussian sampled quadratic energy to bound the expected nonnegative square of the actual original centered source overhang by Gaussian variance times physical gap plus one mesh. This closes the hSampleBound interface required by Proved ef79ef96 before passing to physical clocks. Bounded time-value integrability remains explicit and is justified by genuine stopping-time measurability and finite clock bounds, not an arbitrary floor.
-- source:
--   Proved a05b87a9 original coupled ceiling pair; Proved e916b990 original sampled squared energy lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_two_physical_clocks_common_ceiling_pair
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_sampled_stop_gaussian_energy_lintegral

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_common_ceiling_pair_sampled_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0) (hτρ : ∀ ω, τ ω ≤ ρ ω)
    (ε : ℝ≥0) (hGap : ∀ ω, ρ ω ≤ τ ω + ε)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (Kτ Kρ : Ω → ℕ)
    (hKτ : IsStoppingTime 𝓖 (fun ω => (Kτ ω : WithTop ℕ)))
    (hKρ : IsStoppingTime 𝓖 (fun ω => (Kρ ω : WithTop ℕ)))
    (δ : ℝ≥0)
    (hCeilτ : ∀ ω, τ ω ≤ grid (Kτ ω) ∧ grid (Kτ ω) ≤ τ ω + δ)
    (hCeilρ : ∀ ω, ρ ω ≤ grid (Kρ ω) ∧ grid (Kρ ω) ≤ ρ ω + δ)
    (N : ℕ) (hBound : ∀ ω, max (Kτ ω) (Kρ ω) ≤ N)
    (hTimeA : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2)
      (fun ω => ((min (Kτ ω) (Kρ ω)) : WithTop ℕ))) P)
    (hTimeB : Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2)
      (fun ω => ((max (Kτ ω) (Kρ ω)) : WithTop ℕ))) P) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (grid (max (Kτ ω) (Kρ ω))) ω -
          (grid (max (Kτ ω) (Kρ ω)) : ℝ) * X.c) -
        (X.X (grid (min (Kτ ω) (Kρ ω))) ω -
          (grid (min (Kτ ω) (Kρ ω)) : ℝ) * X.c)) ^ 2) ∂P) ≤
      ENNReal.ofReal (((ε : ℝ) + (δ : ℝ)) * X.σ ^ 2) := by sorry
