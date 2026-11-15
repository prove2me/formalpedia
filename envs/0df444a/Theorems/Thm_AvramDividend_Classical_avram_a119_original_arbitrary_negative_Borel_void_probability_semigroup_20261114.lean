-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a119_original_arbitrary_negative_Borel_void_probability_semigroup_20261114
-- name    : AvramDividend.Classical.avram_a119_original_arbitrary_negative_Borel_void_probability_semigroup_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:23:36.974129+00:00
-- url     : https://prove2.me/theorems/80ebbded-04a0-429d-b76b-0cca68c385e3
-- title:
--   Original physical marked-jump void probabilities form a source-stationary multiplicative semigroup for every Borel mark set
-- statement:
--   The no-physical-marked-jump probability of a combined horizon s+T factors as the product of the no-jump probabilities on s and T for any Borel marks B, whenever the original early no-jump event is measurable in raw F_s. This generalises the Proved negative-band semigroup to arbitrary mark sets using source pathwise split, raw-past/future independence and source stationary mark count law, with no auxiliary probability space.
-- source:
--   Proved wave7_06 arbitrary future Borel mark void/past factor; Proved arbitrary Borel void stationarity c64a7b2a; Proved raw void measurability 0b92926a; new A118 pathwise adjacent-horizon marked-void split. Adapt exact Proved wave7_06 negative-band multiplicative semigroup proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a119_original_arbitrary_negative_Borel_void_probability_semigroup_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hPast : MeasurableSet[𝓕 s]
      {ω : Ω | NX ω (Ioc 0 s ×ˢ B) = 0}) :
    P {ω : Ω | NX ω (Ioc 0 (s + T) ×ˢ B) = 0} =
      P {ω : Ω | NX ω (Ioc 0 s ×ˢ B) = 0} *
      P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by sorry
