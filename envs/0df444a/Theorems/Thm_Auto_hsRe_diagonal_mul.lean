-- Prove2me | Theorems.Thm_Auto_hsRe_diagonal_mul
-- name    : Auto.hsRe_diagonal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:38.019323+00:00
-- url     : https://prove2.me/theorems/eb4a9051-a444-4e5e-ad1d-6192623ef42f
-- title:
--   Auto: hs Re diagonal mul
-- statement:
--   The Auto construction uses the hs Re diagonal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L802-L808
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L802-L808

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

theorem Auto.hsRe_diagonal_mul (a : n → ℝ) (X : Matrix n n ℂ) :
    hsRe X (diagonal (fun i => (a i : ℂ)) * X) = ∑ i, ∑ j, a i * ‖X i j‖ ^ 2 := by sorry
