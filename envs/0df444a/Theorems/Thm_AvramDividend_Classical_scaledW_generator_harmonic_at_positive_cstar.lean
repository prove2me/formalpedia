-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaledW_generator_harmonic_at_positive_cstar
-- name    : AvramDividend.Classical.scaledW_generator_harmonic_at_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:29:09.292775+00:00
-- url     : https://prove2.me/theorems/e15c1757-2765-413a-b469-c2b6d3ff42ed
-- title:
--   Positive optimal barrier: generator harmonicity of scaled scale function at the endpoint
-- statement:
--   At the positive finite optimal barrier a=c*, the scale-function branch u(z)=W(z)/W'(a) (using divE for the formal derivative convention) is integrable in the Lévy generator and q-harmonic, Γu(a)-q u(a)=0. This is the endpoint extension of the existing interior theorem scaled_scaleFunction_q_harmonic_below_cstar, requiring fluctuation-scale regularity and appropriate one-sided analytic control. It is the substantive stochastic part of the HJB generator identity at c*, independent of the above-barrier affine policy.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4 and Theorem 2(ii), generator identity ΓW=qW at the positive optimal barrier, including the Gaussian/BV smoothness alternatives.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem scaledW_generator_harmonic_at_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
      X.generator (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal -
        q * divE (W (cstar W).toReal)
          (scaleDeriv W (cstar W).toReal) = 0 := by
  sorry
end AvramDividend.Classical
