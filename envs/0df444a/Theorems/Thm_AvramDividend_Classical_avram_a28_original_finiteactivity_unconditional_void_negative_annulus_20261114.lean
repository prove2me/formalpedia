-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_finiteactivity_unconditional_void_negative_annulus_20261114
-- name    : AvramDividend.Classical.avram_a28_original_finiteactivity_unconditional_void_negative_annulus_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:50:37.894386+00:00
-- url     : https://prove2.me/theorems/1d35fc59-b6da-4ee5-b141-857d2c36e647
-- title:
--   Original finite-activity actual marked jump measure eventually void on every shrinking negative band at all horizons
-- statement:
--   A genuine original finite-activity spectrally negative Levy source has on one conull event, for each finite horizon, no physical jumps in the omitted shrinking negative mark band after some cutoff, without any extra path-map measurability assumption.
-- source:
--   Proved 9d68c5c2 original jointly measurable mark map, 794fe958 finite-horizon marked void annulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual finite-activity original marked jump count eventually avoids each shrinking negative band. -/

theorem AvramDividend.Classical.avram_a28_original_finiteactivity_unconditional_void_negative_annulus_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ N : ℕ, ∀ n ≥ N,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)) = 0 := by sorry
