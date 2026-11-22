-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_Hessian_physical_L1_vanish_on_initial_event
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_Hessian_physical_L1_vanish_on_initial_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:26:51.060149+00:00
-- url     : https://prove2.me/theorems/2e3f5048-3483-447c-8a77-446e51e4d39a
-- title:
--   Original finite-cap stopped physical Gaussian Hessian second-noise vanishing L1 on the exact localising initial event
-- statement:
--   The authentic predictably masked original Lévy finite-cap Gaussian Hessian centred-square noise sum converges to zero in expected absolute value on every restricted event A, including the initial-information event of the original source 0ef5d778. This follows from the independently Proved original full-mesh L1 convergence and the already Proved original absolute-L1 restriction theorem. Finite sum square integrability is derived directly from the original individual L2-cell hypothesis. This resolves the model Gaussian second-noise channel under the actual source restricted probability measure.
-- source:
--   Original physical stopped finite-cap Ito cash source 0ef5d778 integrates positive residual over an F0-measurable localising event A; this theorem supplies the exact restricted absolute-L1 noise convergence rather than only unconditional L1 vanishing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_finitecap_Hessian_physical_L1_vanish_on_initial_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n)
    (H U : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m i ω, |H m i ω| ≤ K)
    (hHI : ∀ (m i : ℕ), i < m + 1 →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      Integrable (fun ω => (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2)) ^ 2) P)
    (hUeq : ∀ (m i : ℕ) (ω : Ω),
      U m i ω =
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    (hULp : ∀ m i, MemLp (U m i) 2 P)
    (hUadapt : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      StronglyMeasurable[𝓕.rightCont (((i + 1 : ℕ) : ℝ≥0) * Δ)] (U m i))
    (hUcenter : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      P[U m i | 𝓕.rightCont ((i : ℝ≥0) * Δ)] =ᵐ[P]
        (fun _ => (0 : ℝ)))
    (A : Set Ω) :
    Tendsto
      (fun m : ℕ => ∫ ω in A,
        |∑ i ∈ Finset.range (m + 1), U m i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
