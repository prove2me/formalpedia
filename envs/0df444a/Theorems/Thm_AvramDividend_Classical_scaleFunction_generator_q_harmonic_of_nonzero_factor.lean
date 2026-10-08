-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T23:23:02.247014+00:00
-- url     : https://prove2.me/theorems/e8fbc763-da83-4909-b759-27feee641e80
-- title:
--   q-harmonicity of W when the barrier normalisation factor is non-zero
-- statement:
--   Core analytic obligation for Lemma 4. Let W be the q-scale function and let a=(cstar W).toReal>0 in the nonempty interval case. Suppose the normalisation k=divE 1 (scaleDeriv W a) is non-zero. The candidate vcstar is kW below a, so the prescribed C² regularity of vcstar, when needed in the infinite-variation no-Gaussian case, transfers to W. Under the standing and alternative smoothness assumptions, the compensated Lévy generator jump integral of W converges for 0<x<a and (Γ-q)W(x)=0. This is the paper's stopped-martingale-plus-Itô step before multiplication by k. The nonzero-factor hypothesis is essential to transfer the explicitly assumed regularity of vcstar to W. If k=0 the scaled function itself vanishes and needs no harmonicity of W. The independent algebraic theorem generator_const_mul_of_integrable transfers the conclusion to kW.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the Optimal Dividend Problem for a Spectrally Negative Lévy Process I, Proof of Lemma 4, page 21 of arXiv:math/0702893v1; and the q-scale martingale identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
