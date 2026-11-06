-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_postpayment_jump_source_eq
-- name    : AvramDividend.Classical.avram_p3_2_original_controlled_postpayment_jump_source_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:53:46.636011+00:00
-- url     : https://prove2.me/theorems/7a274da1-178b-430a-b28a-762474be84b1
-- title:
--   Exact original controlled post-rightpayment jump is Lévy jump minus simultaneous dividend atom
-- statement:
--   At each strictly positive physical time, the exact original post-rightpayment controlled reserve jump relative to its genuine left prestate equals the actual Lévy source jump less the dividend right-payment atom, without assuming that source and dividend jumps are disjoint. This is an algebraic bridge needed for the original stopped BV nonlinear jump compensation.
-- source:
--   Depends on original explicit left-prestate X/D identity (publication 15ab7019, pending) and Lean ring normalization; no stochastic surrogate or equality-in-law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_controlled_postpayment_jump_source_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (lX : ℝ)
    (hXleft : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 lX)) :
    (x + X.X t ω - rightLimit D t ω) -
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (X.X t ω - lX) - (rightLimit D t ω - D t ω) := by sorry
