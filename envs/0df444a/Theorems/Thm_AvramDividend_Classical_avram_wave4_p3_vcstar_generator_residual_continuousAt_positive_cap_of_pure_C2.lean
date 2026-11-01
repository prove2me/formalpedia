-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:46:09.066958+00:00
-- url     : https://prove2.me/theorems/a979ad51-e582-4380-8bfd-712badb396ae
-- title:
--   Actual Lévy generator residual is continuous at positive optimal barrier in pure-jump unbounded-variation C² branch
-- statement:
--   For the original spectrally negative Levy process, under Standing, q>0, a finite strictly positive optimal barrier, Gaussian coefficient zero, non-bounded-variation paths and global positive-state C2 regularity of the actual capped candidate, the real-valued compensated generator residual is continuous at the barrier from both sides. The non-BV condition forces W(0)=0, which glues the zero-extended candidate continuously at reserve zero and accommodates jumps landing exactly on zero. Compact-local uniform compensated O(min(1,y²)) domination proves continuity of the jump integral. This is the mathematically substantive missing endpoint interface; it does not assume the still-Open interior harmonicity.
-- source:
--   Avram, Palmowski and Pistorius (2007), strict interior generator harmonicity Lemma 4 and separate endpoint regularity. Exact Levy triplet continuity follows from proved finite truncated quadratic moment, generic P3 uniform C2 envelope and residual-continuity children, and source zero-origin theorem 1f6cbd4d. Parent generator equality 91803827 and HJB endpoint 8d03da6b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousAt
      (fun x : ℝ => X.generator (vcstar W) x - q * vcstar W x)
      (cstar W).toReal := by sorry
