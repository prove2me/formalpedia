-- Prove2me | Theorems.Thm_Auto_matCost_toReal_eq
-- name    : Auto.matCost_toReal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:23.29113+00:00
-- url     : https://prove2.me/theorems/aa2c0e5d-19ab-49c1-8891-20029b2dd6a0
-- title:
--   Auto: mat Cost to Real eq
-- statement:
--   The Auto construction uses the mat Cost to Real eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1034-L1056
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1034-L1056

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

theorem Auto.matCost_toReal_eq {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCost P K ≠ ⊤ ∧ (matCost P K).toReal = ∑ i, ∑ j, (3 / 2) * ‖eigCoord hP.1 K i j‖ ^ 2 /
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by sorry
