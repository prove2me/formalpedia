-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja36_original_negative_borel_cell_factorial_moment
-- name    : AvramDividend.Classical.avram_ja36_original_negative_borel_cell_factorial_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T22:37:58.262721+00:00
-- url     : https://prove2.me/theorems/6d1258a3-4cb1-44e0-b4b2-85e5783c509b
-- title:
--   True original negative Borel mark count has factorial second moment (T ν(B))²
-- statement:
--   For an arbitrary measurable negative Borel jump-mark cell on the original finite-activity Levy process, the count's factorial pair moment E[N(N−1)] is the square of the physical Levy intensity. This is precisely the remaining source-probabilistic component of the Poisson variance theorem, after the original real-valued mean and integrability were Proved. Requires a source chronological pair-count argument for arbitrary negative marks, rather than only harmonic annuli.
-- source:
--   Original source pair moment of arbitrary negative Borel mark jumps, parent JA32. Inputs JA34 and JA35 prove the linear mean; Proved generic factorial-to-variance e77e3668 handles algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja36_original_negative_borel_cell_factorial_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    let J : Ω → ℝ := fun ω => (N ω).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => J ω * (J ω - 1)) P ∧
      (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2 := by sorry
