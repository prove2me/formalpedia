-- Prove2me | Theorems.Thm_Auto_fourierPartialSum_exp
-- name    : Auto.fourierPartialSum_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:43.88869+00:00
-- url     : https://prove2.me/theorems/aa6714f5-0926-40c0-95db-84a617100d52
-- title:
--   Auto: fourier Partial Sum exp
-- statement:
--   The Auto construction uses the fourier Partial Sum exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L918-L923
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L918-L923

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

theorem Auto.fourierPartialSum_exp {k : ℤ} {N : ℕ} (hk : k.natAbs ≤ N) (x : ℝ) :
    fourierPartialSum (fun x => Complex.exp (2 * π * Complex.I * k * x)) N x =
      Complex.exp (2 * π * Complex.I * k * x) := by sorry
