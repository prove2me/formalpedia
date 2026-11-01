-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_ae_interior
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_ae_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:41:04.997987+00:00
-- url     : https://prove2.me/theorems/d4c5f18d-6724-48de-8265-c65632d5f3b6
-- title:
--   Positive optimal-barrier generator equality from almost-everywhere strict-interior harmonicity
-- statement:
--   For the actual source spectrally negative Levy generator, Standing, q>0, IsScaleFunction, finite strictly positive cstar, and the exact three-way smoothness hypothesis, assume only that the generator residual of the true value vcstar vanishes Lebesgue-a.e. on strict interior (0,cstar). Then vcstar belongs to the generator domain at cstar and its residual vanishes there. Gaussian or BV branches have independent canonical exact endpoint equality. In the non-Gaussian unbounded-variation branch, W(0)=0, vcstar is globally continuous and monotone and positive-state C2 gives compact residual continuity by the proved uniform compensated jump envelope. This yields ContinuousOn the full open interior; pinned Mathlib Measure.eqOn_of_ae_eq upgrades a.e. to pointwise, and P3's already-Proved exact endpoint-from-interior theorem passes to the cap. This is a genuine weaker interface for the Laplace-uniqueness a.e. source route, without importing Chat 05/P2 Open theorems or silently strengthening smoothness.
-- source:
--   Avram Palmowski Pistorius (2007), Lemma 4 open-interior harmonicity, not an endpoint assertion; Kuznetsov Kyprianou Rivero (2013) generator domain. Proved P3 bcd7380e conditional endpoint, d574f843 compensated generator compact continuity, d2afd925 Gaussian/BV endpoint, scale zero-origin/monotonicity; pinned Mathlib MeasureTheory.Measure.eqOn_of_ae_eq. Complete 113-line source work/avram_wave4_p3_cap_eq_of_ae_interior_private_probe.lean passed exact-revision remote private elaboration to intentional sentinel job a65a94df-46b5-46af-8699-6cb28428d7b5, candidate_error_lines=[]; this is not canonical proof acceptance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cstar_of_ae_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
