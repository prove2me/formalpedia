-- Prove2me | Theorems.Thm_Auto_matCostBil_eq
-- name    : Auto.matCostBil_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:46.701363+00:00
-- url     : https://prove2.me/theorems/6da283ec-8b67-4663-a4d4-e42055343bdb
-- title:
--   Auto: mat Cost Bil eq
-- statement:
--   The Auto construction uses the mat Cost Bil eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1066-L1083
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1066-L1083

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]

theorem Auto.matCostBil_eq {P : Matrix n n ℂ} (hP : P.PosDef) (K L : Matrix n n ℂ) :
    matCostBil P K L = ∑ i, ∑ j, (3 / 2) * ((starRingEnd ℂ) (eigCoord hP.1 K i j) * eigCoord
      hP.1 L i j).re / (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by sorry
