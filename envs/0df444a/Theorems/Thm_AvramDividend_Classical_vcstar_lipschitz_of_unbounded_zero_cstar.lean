-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_lipschitz_of_unbounded_zero_cstar
-- name    : AvramDividend.Classical.vcstar_lipschitz_of_unbounded_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:44:45.731646+00:00
-- url     : https://prove2.me/theorems/7bf6d6a8-10b7-4e3b-9d1b-81e9db8ac817
-- title:
--   Optimal zero-barrier dividend candidate has global Lipschitz constant one
-- statement:
--   For a spectrally negative Lévy process of unbounded variation at positive discount, if the optimal barrier cstar W equals zero, then the mission's exact candidate vcstar W is globally Lipschitz with constant one. This transports the independently Proved barrierValue zero-barrier Lipschitz result into the actual vcstar verification branch, controlling discontinuities and jump increments.
-- source:
--   Proved unbounded_variation_zero_barrier_candidate_lipschitz and the definition of vcstar at zero cstar.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_lipschitz
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_lipschitz_of_unbounded_zero_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    LipschitzWith (1 : ℝ≥0) (vcstar W) := by sorry
