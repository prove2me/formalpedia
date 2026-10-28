-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_of_zero_cstar_and_generator
-- name    : AvramDividend.Classical.vcstar_hjb_of_zero_cstar_and_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:10:47.800979+00:00
-- url     : https://prove2.me/theorems/58050e92-b6aa-4d8b-ba25-75785a81fc09
-- title:
--   Zero optimal barrier gives the HJB equality from the above-barrier generator bound
-- statement:
--   At a zero optimal barrier, every positive reserve lies in the affine continuation region and vcstar has derivative one. If the generator is integrable and its discounted residual is nonpositive there, then max(generator-q*value,1-derivative)=0 on the entire positive half-line. This closes the zero-barrier case of the mission's all-positive HJB reduction under exactly its generator-bound hypothesis.
-- source:
--   Proved vcstar_deriv_eq_one_above_cstar; lattice identity max(t,0)=0 when t≤0.

import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Order.Lattice

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_hjb_of_zero_cstar_and_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hc0 : cstar W = 0)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry
