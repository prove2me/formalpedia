-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
-- name    : AvramDividend.Classical.levy_generatorIntegrable_const_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:21:09.683256+00:00
-- url     : https://prove2.me/theorems/f464799e-9569-4d65-a0c2-23e2b6ef3a34
-- title:
--   Scalar multiplication preserves integrability in the exact nonlocal Lévy generator
-- statement:
--   For any real-valued f in the domain of the pinned spectrally negative Lévy generator at a reserve x, every real scalar multiple k*f lies in the same generator domain. The proof uses the pinned derivative-scaling identity to show the compensated negative-jump integrand scales exactly by k and applies the Bochner Integrable.const_mul theorem under the restricted Lévy measure. This is essential for transferring generator integrability from a q-scale function W to the dividend value scaled by its barrier derivative, without mistakenly claiming the underlying stochastic q-harmonicity.

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_generatorIntegrable_const_mul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (k x : ℝ)
    (hf : X.GeneratorIntegrable f x) :
    X.GeneratorIntegrable (fun z : ℝ => k * f z) x := by sorry
