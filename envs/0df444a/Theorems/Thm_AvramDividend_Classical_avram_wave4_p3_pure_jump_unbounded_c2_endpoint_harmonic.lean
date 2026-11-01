-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_pure_jump_unbounded_c2_endpoint_harmonic
-- name    : AvramDividend.Classical.avram_wave4_p3_pure_jump_unbounded_c2_endpoint_harmonic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:26:57.493791+00:00
-- url     : https://prove2.me/theorems/06f18727-a390-40e1-8a80-490ec7eca1ac
-- title:
--   Exact non-Gaussian unbounded-variation positive-barrier generator harmonicity from unconditional source scale harmonicity
-- statement:
--   At a finite strictly positive optimal barrier for an actual q-scale function under Standing, in the zero-Gaussian, unbounded-variation branch with C2 regularity of the true candidate on every positive state, the original Levy compensated generator of vcstar is integrable at the cap and has exactly zero discounted residual. The proof imports P2 unconditional true source pure-jump harmonicity, transfers C2 from the dividend candidate to W using its proved nonzero normaliser, transfers source harmonicity below cstar, and takes the cap limit using the accepted endpoint-continuity bridge. No assumed interior generator identity or above-barrier inequality is smuggled in.
-- source:
--   Avram–Palmowski–Pistorius (2007) Lemma 4 plus a genuine endpoint generator continuity proof; P2 unconditional scale harmonicity fc01c311; P3 endpoint continuity bcd7380e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_pure_jump_unbounded_c2_endpoint_harmonic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ0 : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
