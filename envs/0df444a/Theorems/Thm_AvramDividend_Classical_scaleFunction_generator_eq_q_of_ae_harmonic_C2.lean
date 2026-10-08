-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_harmonic_C2
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_harmonic_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:30:21.77766+00:00
-- url     : https://prove2.me/theorems/9ccb1afa-1035-4230-b233-d67ec9660ad9
-- title:
--   Almost-everywhere Lévy generator q-harmonicity implies pointwise q-harmonicity on a C2 interval
-- statement:
--   Let W be a q-scale function C2 on (0,a) for a spectrally negative Lévy process satisfying the standing conditions. If W(0)=0 or X has bounded variation, and the generator residual ΓW−qW vanishes Lebesgue almost everywhere in (0,a), then it vanishes at every interior point. Uses the accepted compact continuity results for both branches, compact-to-open continuity and local a.e.-to-pointwise vanishing. The a.e. harmonicity remains an explicit hypothesis.
-- source:
--   Closure of compact-generator continuity and local a.e.-to-pointwise vanishing for Avram Dividend Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_ae_harmonic_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
