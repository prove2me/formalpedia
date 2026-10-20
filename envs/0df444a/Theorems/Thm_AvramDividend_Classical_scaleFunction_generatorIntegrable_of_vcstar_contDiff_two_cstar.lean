-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:02:52.809275+00:00
-- url     : https://prove2.me/theorems/00e5abc9-3d08-47ce-89a6-7c3db419631c
-- title:
--   Jump-integrability of the q-scale function below c* from explicit C2 regularity of the barrier candidate
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function, and let c* > 0 be the optimal barrier. Suppose the barrier value candidate v_{c*} is C^2 on (0, c*) and suppose the barrier normalisation factor divE 1 (scaleDeriv W (cstar W).toReal) is non-zero. Then the jump integral of the Levy generator of W converges at every x in (0, c*): X.GeneratorIntegrable W x holds there. This is the C^2 branch of the convergence of the jump integral of the generator of the dividend candidate, isolated from the remaining branches in which regularity of W itself must first be established (the Gaussian case sigma > 0 and the bounded-variation case). It supplies the generator-domain half of the analytic core of Lemma 4 of Avram, the exact q-harmonicity of W below c* being the other half.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the jump integral of the generator converges on (0, c*) under the smoothness proviso, and the C^2 case is the direct Itô/Stieltjes route used there.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
