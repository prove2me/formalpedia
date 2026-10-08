-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_generatorIntegrable
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_generatorIntegrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T20:57:56.061305+00:00
-- url     : https://prove2.me/theorems/47e1697b-cdff-48d1-8d28-8bec4ecb7ba1
-- title:
--   q-harmonic generator identity for an integrable scale function
-- statement:
--   Stochastic half of the scale-function generator theorem. Let W be the q-scale function on a positive interval (0,a), under the standing hypotheses and the smoothness alternatives required for the appropriate Itô formula. Assume separately that its compensated Lévy generator jump integral converges at every interior point. Then W satisfies (Γ-q)W=0 throughout (0,a). The proof is the source's stopped q-scale martingale argument: stop exp(-qt)W(x+X_t) at the first exit from a compact subinterval around x, apply Itô's formula/Dynkin's formula, use the scale-function two-sided exit martingale identity and then localise to identify the drift with (Γ-q)W(x).
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Lemma 4, p. 21, together with the q-scale two-sided exit martingale identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_generatorIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
