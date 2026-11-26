-- Prove2me | solution 1 for polynomial_eq_zero_of_polynomialSupNorm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:22.655253+00:00
-- url     : https://prove2.me/submissions/6fc1197d-eb49-43a5-9753-026d5322b1af

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_eval_le_polynomialSupNorm
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u
theorem _root_.solution
    (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) (hKinf : K.Infinite)
    (hzero : polynomialSupNorm p K = 0) : p = 0 := by
  apply p.eq_of_infinite_eval_eq 0
  apply hKinf.mono
  intro z hz
  have hle : ‖p.eval z‖ ≤ 0 := by
    simpa only [hzero] using norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz
  have hpz : p.eval z = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  change p.eval z = Polynomial.eval z (0 : ℂ[X])
  simpa only [eval_zero] using hpz
