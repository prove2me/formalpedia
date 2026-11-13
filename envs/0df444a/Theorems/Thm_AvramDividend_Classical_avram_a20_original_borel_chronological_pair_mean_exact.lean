-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_chronological_pair_mean_exact
-- name    : AvramDividend.Classical.avram_a20_original_borel_chronological_pair_mean_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:39:13.979786+00:00
-- url     : https://prove2.me/theorems/7ab3ac70-7092-4431-af03-61a1c80da1e1
-- title:
--   Exact genuine original arbitrary negative Borel chronological marked-jump pair expectation
-- statement:
--   For each spectrally negative Lévy process with finite total negative jump intensity and every measurable negative Borel mark set B, the genuine same-original-sample chronological marked jump pair count, expressed as the cardinal of ordered distinct marked jump times, is integrable and has expected twice-pair count exactly (T ν(B))². This is the physical source moment underlying JA36. Derive it from Proved original chronological past-future rectangle count products, finite intrinsic jump-time grid separation and dominated convergence, without introducing a canonical process or postulating a Poisson count law. It extends an already Proved full-negative-cutoff chronological pair moment to arbitrary negative Borel cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_chronological_pair_mean_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω =>
      ((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
      (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by sorry
