-- Prove2me | Theorems.Thm_Auto_hasDerivAt_gweightD1_p
-- name    : Auto.hasDerivAt_gweightD1_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:35.852403+00:00
-- url     : https://prove2.me/theorems/cc8f8896-0ecb-4b8f-9efe-7218735099a5
-- title:
--   Auto: has Deriv At gweight D1 p
-- statement:
--   The Auto construction uses the has Deriv At gweight D1 p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3000-L3004
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3000-L3004

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι]

theorem Auto.hasDerivAt_gweightD1_p (u : ι → ℝ) (h σ p : ℝ) (i : ι) :
    HasDerivAt (fun q => -(h * gaussianD 1 σ (u i - q))) (h * gaussianD 2 σ (u i - p)) p := by sorry
