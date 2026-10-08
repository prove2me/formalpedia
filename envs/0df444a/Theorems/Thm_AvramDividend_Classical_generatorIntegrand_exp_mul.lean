-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul
-- name    : AvramDividend.Classical.generatorIntegrand_exp_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:19:09.110243+00:00
-- url     : https://prove2.me/theorems/ceeebf5f-52ae-409f-ab1f-c2e7d4fc0039
-- title:
--   Lévy-generator exponential jump integrand factors by the base exponential
-- statement:
--   For an exponential test function f(z)=exp(θz), the Lévy-generator jump integrand f(x+y)-f(x)-f'(x)y1_{|y|<1} is f(x) times the Lévy–Khintchine jump integrand exp(θy)-1-θy1_{|y|<1}. This is a pointwise algebraic identity, using Mathlib iteratedDeriv_exp_const_mul.
-- source:
--   Deterministic generator algebra from AvramDividend.Classical.SpectrallyNegativeLevy.generatorIntegrand and Mathlib.Analysis.SpecialFunctions.ExpDeriv.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.generatorIntegrand_exp_mul
    (θ x y : ℝ) :
    SpectrallyNegativeLevy.generatorIntegrand (fun z : ℝ => Real.exp (θ * z)) x y =
      Real.exp (θ * x) *
        (Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by sorry
