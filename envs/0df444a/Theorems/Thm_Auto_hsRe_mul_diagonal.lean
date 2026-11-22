-- Prove2me | Theorems.Thm_Auto_hsRe_mul_diagonal
-- name    : Auto.hsRe_mul_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:50.175813+00:00
-- url     : https://prove2.me/theorems/59310c2e-98e3-4937-b5cf-f6940ab1e27e
-- title:
--   Auto: hs Re mul diagonal
-- statement:
--   The Auto construction uses the hs Re mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L811-L817
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L811-L817

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

theorem Auto.hsRe_mul_diagonal (a : n → ℝ) (X : Matrix n n ℂ) :
    hsRe X (X * diagonal (fun i => (a i : ℂ))) = ∑ i, ∑ j, a j * ‖X i j‖ ^ 2 := by sorry
