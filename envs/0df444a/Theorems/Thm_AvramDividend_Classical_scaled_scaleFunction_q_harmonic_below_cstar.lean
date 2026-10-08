-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaled_scaleFunction_q_harmonic_below_cstar
-- name    : AvramDividend.Classical.scaled_scaleFunction_q_harmonic_below_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T23:09:49.983992+00:00
-- url     : https://prove2.me/theorems/c8630e24-eb5a-4abc-884d-004cd0e50994
-- title:
--   Analytic q-harmonicity of the scaled scale function below c*
-- statement:
--   Let W be the q-scale function under the standing and local smoothness assumptions of Lemma 4. With a=(cstar W).toReal, define U(z)=divE (W z) (scaleDeriv W a), the scale-function formula for the barrier candidate on the lower branch. For each 0<x<a, the negative-jump generator integral of U converges and ΓU(x)-q U(x)=0. This isolates the substantive analytic conclusion obtained from the Laplace characterisation of W, the Lévy-Khintchine generator and Ito/resolvent reasoning. In particular, it preserves the paper's exceptional conventions for extended-real scale derivatives and the stated disjunctive smoothness condition. The companion generator_eq_of_agree_below lemma then transfers this harmonicity to vcstar, which agrees with U for all z<a.
-- source:
--   Avram, Palmowski and Pistorius, On the Optimal Dividend Problem for a Spectrally Negative Lévy Process I, arXiv:math/0702893, Lemma 4, p.20, and the scale-function Laplace identity (3.4).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaled_scaleFunction_q_harmonic_below_cstar {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable
          (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x ∧
        X.generator
            (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x -
          q * divE (W x) (scaleDeriv W (cstar W).toReal) = 0 := by sorry

end AvramDividend.Classical
