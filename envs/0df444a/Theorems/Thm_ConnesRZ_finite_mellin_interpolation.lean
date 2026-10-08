-- Prove2me | Theorems.Thm_ConnesRZ_finite_mellin_interpolation
-- name    : ConnesRZ.finite_mellin_interpolation
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T20:55:40.115244+00:00
-- url     : https://prove2.me/theorems/f5686920-2f14-4d9c-b727-45909ddc1a5f
-- title:
--   Finite Mellin interpolation on smooth compactly supported test functions
-- statement:
--   For any finite family of distinct complex points and any prescribed complex values, there is a smooth compactly supported function whose shifted Mellin transform takes exactly those values. No uniform support bound is imposed. This is the finite interpolation step in Burnol’s localization proof of Weil’s positivity criterion.
-- source:
--   Jean-François Burnol, The Explicit Formula in simple terms, https://arxiv.org/abs/math/9810169v2 , pp. 5–6, section Weil’s positivity criterion and stochastic processes: the interpolation argument using the differential operator and distinct eigenvalues. Translated to additive coordinates and the half-shift of ConnesRZ.mellinHat.

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem finite_mellin_interpolation {ι : Type*} [Finite ι] (z : ι → ℂ) (hz : Function.Injective z)
    (a : ι → ℂ) : ∃ g : ℝ → ℂ, IsTest g ∧ ∀ i, mellinHat g (z i) = a i := by sorry

end ConnesRZ
