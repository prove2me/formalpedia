-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_physical_Hessian_cross_L1
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_physical_Hessian_cross_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:07:07.857057+00:00
-- url     : https://prove2.me/theorems/7e470c61-42fe-46de-8b7d-58c40f81c733
-- title:
--   Original finite-cap true stopped Gaussian Hessian raw-minus-centred square cross L1 limit
-- statement:
--   For the original stopped Gaussian physical-grid caplinear upper truncation b, the expected absolute Hessian-weighted difference of raw and drift-centred squared Lévy increments vanishes, provided the true active pre-stopping Hessian coefficients have a uniform bound and the weighted sums are integrable. Apply proved source-specific Gaussian cross limit ba8830b1, retaining exact s<rho and s+Delta<=rho fullcell mask, postpayment rightLimit D, and the source if Y<=b then w second derivative else zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_finitecap_physical_Hessian_cross_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (b q : ℝ)
    (hBound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω → s + Δ ≤ ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
             else 0) / 2 * (R ^ 2 - Z ^ 2)
        else 0)
    (∀ m, Integrable (fun ω => |B m ω|) P) →
    Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
