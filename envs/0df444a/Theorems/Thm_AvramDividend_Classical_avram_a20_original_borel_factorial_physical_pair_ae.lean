-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_factorial_physical_pair_ae
-- name    : AvramDividend.Classical.avram_a20_original_borel_factorial_physical_pair_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:38:53.39957+00:00
-- url     : https://prove2.me/theorems/99249e6e-cc9f-4928-abf3-bbf460b487fc
-- title:
--   Original negative Borel marked-count factorial equals twice genuine chronological jump pairs a.e.
-- statement:
--   For the literal original spectrally negative Lévy physical process with finite total negative activity and every measurable negative Borel set B, the real factorial count J(J−1) equals twice the number of chronological distinct marked jump-time pairs on the same sample path, almost everywhere. Derive the finite-time marked jump set and its cardinal using the Proved intrinsic original count ENat cardinal equality and source almost-sure finite count. The finite combinatorics uses the Proved Mathlib card_product_filter_lt and natural-number choose-two identities. This supplies the pathwise algebra needed to calculate JA36 from a genuine original chronological pair expectation instead of an additional Poisson-law assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_factorial_physical_pair_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let S : Ω → Set ℝ≥0 := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    ∀ᵐ ω ∂P, (N ω).toReal * ((N ω).toReal - 1) =
      2 * ((((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard) : ℝ) := by sorry
