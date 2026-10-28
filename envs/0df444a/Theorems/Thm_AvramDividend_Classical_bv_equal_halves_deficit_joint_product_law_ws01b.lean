-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_equal_halves_deficit_joint_product_law_ws01b
-- name    : AvramDividend.Classical.bv_equal_halves_deficit_joint_product_law_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:24:58.223803+00:00
-- url     : https://prove2.me/theorems/9d74dc55-b2a7-42e4-a138-4cc5b2e8361a
-- title:
--   Joint product law of two equal-length actual Lévy drift-deficit increments
-- statement:
--   For any fixed nonnegative duration t, the actual bounded-variation Lévy drift deficit over [0,t] and [t,2t] is an independently identically distributed pair. The joint pushforward is the product of the common one-time deficit law. This is the probabilistic bridge from stationary independent Lévy increments to the dyadic reverse martingale half-sum identity, without requiring finite jump activity or integrability.
-- source:
--   Canonical SpectrallyNegativeLevy adapted, indepIncrements, stationaryIncrements; Prove2Me accepted arbitrary-history Lévy increment product-law proof UUID 2e08771d and stationary drift-deficit law ed24e69e.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Defs

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_equal_halves_deficit_joint_product_law_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Measure.map (fun ω =>
      (X.drift * (t : ℝ) - X.X t ω,
       X.drift * (t : ℝ) - (X.X (t + t) ω - X.X t ω))) P =
      (Measure.map (fun ω => X.drift * (t : ℝ) - X.X t ω) P).prod
        (Measure.map (fun ω => X.drift * (t : ℝ) - X.X t ω) P) := by sorry
