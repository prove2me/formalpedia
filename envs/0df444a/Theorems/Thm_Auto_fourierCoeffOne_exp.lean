-- Prove2me | Theorems.Thm_Auto_fourierCoeffOne_exp
-- name    : Auto.fourierCoeffOne_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:40.825246+00:00
-- url     : https://prove2.me/theorems/87fd1a9b-dd2f-4dbb-9a21-5763379b28f0
-- title:
--   Auto: fourier Coeff One exp
-- statement:
--   The Auto construction uses the fourier Coeff One exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L895-L916
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L895-L916

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

theorem Auto.fourierCoeffOne_exp (k n : ℤ) :
    fourierCoeffOne (fun x => Complex.exp (2 * π * Complex.I * k * x)) n =
      if n = k then 1 else 0 := by sorry
