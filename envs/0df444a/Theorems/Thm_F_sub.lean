-- Prove2me | Theorems.Thm_F_sub
-- name    : F_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:07.102196+00:00
-- url     : https://prove2.me/theorems/57fa60b6-964c-47e9-8e9a-a2968f7525ee
-- title:
--   F sub: F sub
-- statement:
--   The F sub construction uses the F sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L22-L24
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L22-L24

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Theorems.Thm_W21_hf

set_option autoImplicit true
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

theorem F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by sorry
