-- Prove2me | Theorems.Thm_Auto_fourierPartialSum_eq_integral
-- name    : Auto.fourierPartialSum_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:40.421834+00:00
-- url     : https://prove2.me/theorems/7f34728f-0e25-482c-bb87-27913a28ea8c
-- title:
--   Auto: fourier Partial Sum eq integral
-- statement:
--   The Auto construction uses the fourier Partial Sum eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L813-L839
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L813-L839

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real

theorem Auto.fourierPartialSum_eq_integral {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1)
    (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = ∫ s in (-(1 / 2) : ℝ)..(1 / 2), f (x - s) * dirichletKernel N s := by sorry
