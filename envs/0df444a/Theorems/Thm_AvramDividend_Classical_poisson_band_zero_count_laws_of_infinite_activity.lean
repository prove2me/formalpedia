-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_band_zero_count_laws_of_infinite_activity
-- name    : AvramDividend.Classical.poisson_band_zero_count_laws_of_infinite_activity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-27T15:41:29.070966+00:00
-- url     : https://prove2.me/theorems/0966bee8-71b3-4ed7-ad8a-abe88f7ae541
-- title:
--   Finite-band Poisson zero-count laws from infinite Levy negative activity
-- statement:
--   Given a spectrally negative Levy process whose negative jump measure is infinite, for any rate sequence delta there exist finite-band jump counters whose zero sets cover the no-jump events and whose zero probabilities follow the Poisson exponential law with band masses. This supplies exactly the (counts, hsubset, hzeroLaw) premises of Proved ae_early_downward_jumps_of_levy_band_zero_count_laws (85823b83), isolating the Poisson-count construction gap in the BV infinite-activity branch of barrierStrategy_zero_boundary_value_identity (c2921c8c).
-- source:
--   Construction gap hCount in the BV infinite-activity branch of c2921c8c: Proved 85823b83 trades Open ff758fb4 for (delta/counts/hsubset/hzeroLaw) plus the order-top hTop bridge; this child fixes the exact binder-mapped counts statement so the parent reduction can reuse delta/hdeltapos/hcofinal and apply 85823b83 then Proved 9228cae3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Filter Topology
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem poisson_band_zero_count_laws_of_infinite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hTop : X.ν (Iio (0 : ℝ)) = ⊤)
    (δ : ℕ → ℝ≥0) :
    ∃ counts : ℕ → ℕ → Ω → ℕ,
      (∀ k n : ℕ,
        {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
          ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
            (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
          ⊆ {ω | counts k n ω = 0}) ∧
      (∀ k n : ℕ,
        P {ω | counts k n ω = 0} =
          ENNReal.ofReal (Real.exp
            (-((δ k : ℝ) *
              (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) := by sorry

end AvramDividend.Classical
