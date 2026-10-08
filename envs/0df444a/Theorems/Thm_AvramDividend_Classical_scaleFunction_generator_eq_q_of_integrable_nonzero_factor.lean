-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_integrable_nonzero_factor
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_integrable_nonzero_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:10:18.318864+00:00
-- url     : https://prove2.me/theorems/c24f8b38-be09-41f1-92b9-e825f5ac94da
-- title:
--   q-harmonic generator identity once the scale-function jump integral converges
-- statement:
--   Identity half of Lemma 4. Assume the generator jump integral of W converges throughout (0,cstar), in addition to the original standing and smoothness hypotheses and nonzero barrier normalisation. Then W satisfies ΓW(x)-qW(x)=0 on that interval. This isolates the source's genuinely stochastic step: the stopped process exp(-q(t∧T_(0,a))) W(X_(t∧T_(0,a))) is a martingale and Itô's formula identifies the interior drift with (Γ-q)W.
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Lemma 4, p. 21, arXiv:math/0702893v1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_integrable_nonzero_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hint : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
