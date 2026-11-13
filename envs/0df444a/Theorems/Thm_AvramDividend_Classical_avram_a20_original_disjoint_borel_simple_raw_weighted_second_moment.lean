-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
-- name    : AvramDividend.Classical.avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:51:00.755045+00:00
-- url     : https://prove2.me/theorems/c772b553-e199-4de0-9477-5b320fe0e9ee
-- title:
--   True original finite disjoint Borel-mark simple weighted raw first and second moments, exact
-- statement:
--   For any finite family of pairwise disjoint measurable negative Borel mark cells in the actual original spectrally negative Lévy source and real deterministic weights, the weighted raw marked jump count J is integrable and square-integrable, with E[J]=m=∑a_i Tν(B_i), and exact E[J²]=m²+v where v=∑a_i² Tν(B_i). Its centred finite weighted sum has exact zero mean by true-source first moments and exact L² isometry by the already Proved JA31. A general proved centred-square deterministic-shift lemma yields raw second moments, with no Poisson law assumed and no replacement sample process. This is the finite-simple approximation base for the original bounded-mark weighted Poisson integral moments and Gaussian residual strip isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let J : Ω → ℝ := fun ω =>
      ∑ i ∈ F, a i * (NX ω (Ioc 0 T ×ˢ B i)).toReal
    let m : ℝ := ∑ i ∈ F, a i * r i
    let v : ℝ := ∑ i ∈ F, (a i) ^ 2 * r i
    Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
      (∫ ω, J ω ∂P) = m ∧
      (∫ ω, (J ω) ^ 2 ∂P) = m ^ 2 + v := by sorry
