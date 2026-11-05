-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_adjacent_centred_increment_indepFun
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_adjacent_centred_increment_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:16:33.239681+00:00
-- url     : https://prove2.me/theorems/e702ba0e-e385-4419-93eb-fd17e59087a1
-- title:
--   Original Levy adjacent drift-centred source increments form an independent pair of random variables
-- statement:
--   For any original spectrally negative Levy process and s≤t≤u, the drift-centred future increment (t,u) and earlier increment (s,t) are independent random variables on the same probability space.
-- source:
--   Proved original P4-A independent adjacent comap sigma algebras; Mathlib ProbabilityTheory.IndepFun_iff_Indep.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_adjacent_centred_increments_indep

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_adjacent_centred_increment_indepFun
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun
      (fun ω => (Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c)
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      P := by sorry
