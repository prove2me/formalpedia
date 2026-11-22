-- Prove2me | Theorems.Thm_Auto_sqrt_fromBlocks_diag
-- name    : Auto.sqrt_fromBlocks_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:15.826644+00:00
-- url     : https://prove2.me/theorems/c43f729d-c084-4431-9de8-6cf148a2b8dc
-- title:
--   Auto: sqrt from Blocks diag
-- statement:
--   The Auto construction uses the sqrt from Blocks diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3467-L3478
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3467-L3478

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem Auto.sqrt_fromBlocks_diag {ι : Type*} [Fintype ι] {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) :
    open scoped Classical in CFC.sqrt (Matrix.fromBlocks P 0 0 Q) = Matrix.fromBlocks (CFC.sqrt
      P) 0 0 (CFC.sqrt Q) := by sorry
