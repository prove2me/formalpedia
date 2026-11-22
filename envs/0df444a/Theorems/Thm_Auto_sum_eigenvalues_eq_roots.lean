-- Prove2me | Theorems.Thm_Auto_sum_eigenvalues_eq_roots
-- name    : Auto.sum_eigenvalues_eq_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:16.041129+00:00
-- url     : https://prove2.me/theorems/0b2bc2b8-654f-4edf-a661-003c77d9ab74
-- title:
--   Auto: sum eigenvalues eq roots
-- statement:
--   The Auto construction uses the sum eigenvalues eq roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L722-L725
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L722-L725

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

theorem Auto.sum_eigenvalues_eq_roots (g : ℂ → ℝ) {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    ∑ i, g (hP.eigenvalues i) = (P.charpoly.roots.map g).sum := by sorry
