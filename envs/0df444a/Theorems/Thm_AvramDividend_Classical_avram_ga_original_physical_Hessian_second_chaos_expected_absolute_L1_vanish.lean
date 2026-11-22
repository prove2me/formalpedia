-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_physical_Hessian_second_chaos_expected_absolute_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_original_physical_Hessian_second_chaos_expected_absolute_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:16:23.688651+00:00
-- url     : https://prove2.me/theorems/137edad2-b732-4dc5-a6b4-89b04d42e388
-- title:
--   Original stopped finite-cap physical Gaussian Hessian compensated quadratic-noise sum has vanishing expected absolute value
-- statement:
--   For the original standing zero-jump Lévy process, physical grid Δ=n/(m+1), postpayment Hessian coefficients, exact centred squared Gaussian increments, and genuine filtered martingale difference and boundedness hypotheses, the expected absolute value of the full compensated quadratic noise sum tends to zero. Reuse the accepted original-source L² vanishing, finite-sum MemLp closure, and Young L²-to-L¹ convergence. This closes the authentic stopped Gaussian second-chaos positive-error channel without the circular physical cash lemma.
-- source:
--   True original finitecap physical stopped Ito–Stieltjes cash source 0ef5d778: independently controlled compensated Hessian second-chaos L1 channel with physical right-continuous filtration and predictable start-time mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_physical_Hessian_second_chaos_expected_absolute_L1_vanish
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
        (fun _ => (0 : ℝ))) :
    Tendsto
      (fun m : ℕ => ∫ ω,
        |∑ i ∈ Finset.range (m + 1), U m i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
