-- Prove2me | Theorems.Thm_Auto_fourierPartialSum_eq
-- name    : Auto.fourierPartialSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:04:04.120261+00:00
-- url     : https://prove2.me/theorems/17bc0a92-48cd-4236-b25b-739cd81233d8
-- title:
--   Auto: fourier Partial Sum eq
-- statement:
--   The Auto construction uses the fourier Partial Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1463-L1473
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1463-L1473

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

theorem Auto.fourierPartialSum_eq (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    Triangular.fourierPartialSum f N x = fourierPartialSum f N x := by sorry
