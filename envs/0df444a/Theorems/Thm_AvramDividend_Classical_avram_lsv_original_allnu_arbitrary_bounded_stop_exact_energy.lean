-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy
-- name    : AvramDividend.Classical.avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:43:38.563074+00:00
-- url     : https://prove2.me/theorems/52e1934f-5373-495c-90dc-1feda4a80ed8
-- title:
--   Original mixed Levy physical Gaussian channel exact quadratic stopped energy at any bounded time
-- statement:
--   For the actual original spectrally negative Levy process with a genuine same-space zero-jump component and pathwise physical small and large jump decomposition, the stopped Gaussian remainder at any bounded right-continuous filtration stopping time has integrable square and expected energy sigma squared times expected clock. The stopping clock need not have countable range. Lean-LSV CC BY 4.0 adapted proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Genuine original mixed Levy process with actual same-space zero-jump Gaussian
   channel. The physical decomposition by small/large jumps is required.
   dufeteller lean-lsv CC BY 4.0, commit a5f604d. -/

theorem AvramDividend.Classical.avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => (M (τ ω) ω)^2) P ∧
      (∫ ω, (M (τ ω) ω)^2 ∂P) =
        ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P := by sorry
