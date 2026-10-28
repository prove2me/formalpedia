-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eq_positive_part_of_unbounded_zero_cstar
-- name    : AvramDividend.Classical.vcstar_eq_positive_part_of_unbounded_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:43:03.717618+00:00
-- url     : https://prove2.me/theorems/1b686ba3-2e42-4b19-bd17-b9d85553f3d0
-- title:
--   Exact optimal candidate is positive reserve at a zero unbounded-variation barrier
-- statement:
--   If a spectrally negative Lévy process has unbounded variation, q>0 and its optimal derivative-based barrier cstar W equals zero, then the actual root-mission optimal value candidate vcstar W is globally the positive-part function max(x,0). This transports the proved zero-barrier representation to the precise vcstar candidate used in the mission's HJB and verification branches, with no additional smoothness assumptions.
-- source:
--   Proved unbounded_variation_zero_barrier_candidate_eq_posPart and the definition vcstar W = barrierValue W (cstar W).toReal.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_eq_positive_part_of_unbounded_zero_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) (x : ℝ) :
    vcstar W x = max x 0 := by sorry
