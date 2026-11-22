-- Prove2me | Theorems.Thm_Auto_integrable_fin2_prod
-- name    : Auto.integrable_fin2_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:04.121802+00:00
-- url     : https://prove2.me/theorems/5aeba636-092e-403c-9daa-072b56be84d6
-- title:
--   Auto: integrable fin2 prod
-- statement:
--   The Auto construction uses the integrable fin2 prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6286-L6291
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6286-L6291

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.integrable_fin2_prod {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun q : Fin 2 → ℝ => f (q 0) * g (q 1)) := by sorry
