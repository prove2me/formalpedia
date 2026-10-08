-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_const_mul_of_integrable
-- name    : AvramDividend.Classical.generator_const_mul_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:22:08.805282+00:00
-- url     : https://prove2.me/theorems/9dbc820b-0bd9-4ba7-b3ec-c0000a6578b4
-- title:
--   Generator commutes with constant scaling of an integrable function
-- statement:
--   For the classical spectrally negative Lévy generator defined in this mission, suppose the compensated jump integrand of a real-valued function f is integrable at x. For any real constant k, the compensated jump integrand of z↦k f(z) is integrable and Γ(k f)(x)=k Γf(x). This includes k=0, for which the converse integrability implication is false. The result follows directly from scalar linearity of the first and second derivatives and the compensated jump integrand, and from linearity of the Lévy integral. It is a reusable algebraic input for deriving the scaled-scale-function harmonicity required by Lemma 4.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the Optimal Dividend Problem for a Spectrally Negative Lévy Process I, Lemma 4 and the generator definition, pp. 14, 20-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_const_mul_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x k : ℝ)
    (hf : X.GeneratorIntegrable f x) :
    X.GeneratorIntegrable (fun z => k * f z) x ∧
      X.generator (fun z => k * f z) x = k * X.generator f x := by sorry

end AvramDividend.Classical
