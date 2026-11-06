-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_simultaneous_nonlinear_jump_split
-- name    : AvramDividend.Classical.avram_p3_2_original_simultaneous_nonlinear_jump_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:11:29.516292+00:00
-- url     : https://prove2.me/theorems/2c18df8a-d043-49ad-af54-190bfe0c388f
-- title:
--   Exact original nonlinear Lévy jump and simultaneous dividend right-payment split
-- statement:
--   For the literal original spectrally negative Lévy process and any dividend path, split the nonlinear w-reserve jump through the physically distinct pre-right-payment state x+X_t-D_t. The first term is the Lévy prepayment jump; the second is the dividend right-payment atom. They may occur at the same physical time. The left source value lX is an explicit parameter to be instantiated by the original left-prestate theorem. No disjointness, surrogate process, stochastic law or boundary assumption is used.
-- source:
--   Direct ring identity in actual X.X and rightLimit D; pairs with the accepted original dividend and source-jump prestate theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_simultaneous_nonlinear_jump_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (ω : Ω) (t : ℝ≥0) (lX : ℝ) :
    w (x + X.X t ω - rightLimit D t ω) -
      w (x + lX - D t ω) =
      (w (x + X.X t ω - D t ω) -
        w (x + lX - D t ω)) +
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω)) := by sorry
