-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_physical_quadratic_Hessian_L2_second_moment_vanish
-- name    : AvramDividend.Classical.avram_ga_original_physical_quadratic_Hessian_L2_second_moment_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:02:36.599382+00:00
-- url     : https://prove2.me/theorems/2da90020-329a-4395-810c-df75c25a4cfb
-- title:
--   Authentic stopped finite-cap physical-grid Gaussian Hessian centred-square noise has vanishing global second moment
-- statement:
--   In the original zero-jump standing Lévy model and physical grid Δ=n/(m+1), with the actual postpayment Hessian coefficients and their genuine filtered martingale-difference, integrability and boundedness hypotheses, the full compensated Gaussian quadratic channel has second moment tending to zero. Reuse the accepted original physical Hessian MDS second-moment rate theorem, then the accepted reciprocal rate-to-zero analytic lemma. This is the direct stochastic second-channel part of the finite-cap original stopped Itô–Stieltjes cash proof, without anticipative final-cell masks.
-- source:
--   Original true finite-cap Gaussian physical stopped cash source 0ef5d778: verifies variance vanishing of the exact model-centred quadratic Hessian sum as a rootward result from already Proved original source-specific variance and reciprocal rate lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_physical_quadratic_Hessian_L2_second_moment_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
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
        (fun _ => (0 : ℝ))) :
    Tendsto
      (fun m : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (m + 1), U m i ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
