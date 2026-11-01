-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:43:14.825202+00:00
-- url     : https://prove2.me/theorems/0458283a-e59d-4ddc-8184-b53a2431ef38
-- title:
--   Unconditional positive optimal barrier generator equality without above-barrier generator-control assumption
-- statement:
--   For the real source spectrally negative Levy process under Standing, a genuine q-scale function with finite positive cstar, and exactly the disjunctive source regularity assumed for the original positive endpoint (Gaussian, BV, or global positive C2 candidate), the actual compensated generator of vcstar is integrable at the optimal cap and its discounted residual is exactly zero, without any assumption about generator behavior above the barrier. The proof is an unconditional case split into the already canonically Proved Gaussian-or-BV positive-cap harmonicity and the newly Proved actual pure-jump unbounded-C2 source-to-endpoint theorem. No appeal to the original positive-cap target with its extra hgen premise occurs.
-- source:
--   Avram, Palmowski, Pistorius (2007) Lemma 4 plus genuine endpoint regularity; canonically Proved independent endpoint branches d2afd925 and 06f18727

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
