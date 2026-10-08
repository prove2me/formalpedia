-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_integrable_of_nonzero_factor
-- name    : AvramDividend.Classical.scaleFunction_generator_integrable_of_nonzero_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:10:20.868976+00:00
-- url     : https://prove2.me/theorems/44b032f3-3bca-4fa9-b8d6-7ef603787c59
-- title:
--   Generator jump integral of the q-scale function converges below cstar
-- statement:
--   Integrability half of Lemma 4. Under the original standing and smoothness assumptions, and assuming the barrier normalisation factor is nonzero so that explicit C² regularity of vcstar transfers to W, the compensated negative-jump integrand defining the Lévy generator of the q-scale function W is integrable at every x in (0,cstar). This can be proved independently of the stopped martingale identity by splitting jumps near 0 from jumps bounded away from 0: use a Taylor remainder (or first-order remainder in the bounded-variation branch) near zero and finite Lévy mass away from zero.
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Lemma 4 and scale-function smoothness discussion around pp. 14 and 21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_integrable_of_nonzero_factor
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
      X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
