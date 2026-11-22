-- Prove2me | Theorems.Thm_Auto_trF_eq_sum
-- name    : Auto.trF_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:37.236548+00:00
-- url     : https://prove2.me/theorems/246dd236-ae66-4b1a-aad4-a4aa77592348
-- title:
--   Auto: tr F eq sum
-- statement:
--   The Auto construction uses the tr F eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L716-L719
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L716-L719

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
omit [DecidableEq m]

theorem Auto.trF_eq_sum (f : ℝ → ℝ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    trF f P = ∑ i, f (hP.eigenvalues i) := by sorry
