-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrand_add
-- name    : AvramDividend.Classical.levy_generatorIntegrand_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T22:30:13.284124+00:00
-- url     : https://prove2.me/theorems/1db30c73-dbba-4086-b99a-c990ce013aed
-- title:
--   Additivity of the full compensated Lévy generator jump integrand
-- statement:
--   For any two differentiable real payoffs f,g at a reserve x (witnessed by HasDerivAt f a x and HasDerivAt g b x), the full Lévy generator jump integrand at reserve x and jump size y is additive: generatorIntegrand(f+g)(x,y)=generatorIntegrand(f)(x,y)+generatorIntegrand(g)(x,y). This includes exact compensation by the derivative times y 1_{(-1,1)}(y). Derive linearity of the derivative from HasDerivAt.add and the two HasDerivAt.deriv identities, unfold the definition generatorIntegrand, then close by commutative ring arithmetic. This is the pointwise basis for showing Γ is linear on its integrability domain, thus extending already Proved Γ expθ=ψθ expθ from individual exponentials to finite linear combinations. It does not assume an unjustified stopped Ito/Dynkin formula or assert the generator identity for arbitrary C² functions without integrability.
-- source:
--   Pinned Mathlib.Analysis.Calculus.Deriv.Add HasDerivAt.add, derivative identities and the exact mission generatorIntegrand; no unproved imports.

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open AvramDividend.Classical.SpectrallyNegativeLevy

theorem AvramDividend.Classical.levy_generatorIntegrand_add
    (f g : ℝ → ℝ) (a b x y : ℝ)
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    generatorIntegrand (fun z => f z + g z) x y =
      generatorIntegrand f x y + generatorIntegrand g x y := by sorry
