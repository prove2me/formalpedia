-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
-- name    : AvramDividend.Classical.generator_eq_of_agree_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:10:15.281413+00:00
-- url     : https://prove2.me/theorems/db36cebd-0a19-4214-8de0-da55a27b5571
-- title:
--   Generator locality below a barrier for a spectrally negative Lévy process
-- statement:
--   For the spectrally negative Lévy generator Γ defined in the mission, suppose f and g agree at every capital z<a and x<a. Then their generator jump integrands agree ν-almost everywhere, since ν is restricted to negative jumps y<0 and x+y<x<a. Agreement on the open interval (-∞,a) also gives equality of first and second derivatives at x, so Γf(x)=Γg(x). Integrability of the generator jump integral is equivalent for f and g. This lemma isolates the locality step needed to replace the barrier value by its scale-function expression below the barrier, including the integrability conclusion.
-- source:
--   Avram, Palmowski and Pistorius, On the Optimal Dividend Problem for a Spectrally Negative Lévy Process I, arXiv:math/0702893, Lemma 4 and the generator in Section 5; generator locality for spectrally negative jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_eq_of_agree_below {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (f g : ℝ → ℝ)
    (a x : ℝ) (hx : x < a)
    (hfg : ∀ z : ℝ, z < a → f z = g z) :
    (X.GeneratorIntegrable f x ↔ X.GeneratorIntegrable g x) ∧
      X.generator f x = X.generator g x := by sorry

end AvramDividend.Classical
