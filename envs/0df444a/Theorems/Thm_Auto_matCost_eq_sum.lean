-- Prove2me | Theorems.Thm_Auto_matCost_eq_sum
-- name    : Auto.matCost_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:08.361325+00:00
-- url     : https://prove2.me/theorems/7ee77976-98b3-4f6b-b716-2928e12bfb87
-- title:
--   Auto: mat Cost eq sum
-- statement:
--   The Auto construction uses the mat Cost eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1007-L1014
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1007-L1014

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

theorem Auto.matCost_eq_sum {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ∑ i, ∑ j, ENNReal.ofReal ((3 / 2) * ‖(star (hP.1.eigenvectorUnitary : Matrix n
      n ℂ) * K * (hP.1.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2) / ENNReal.ofReal
      (√(hP.1.eigenvalues i) + √(hP.1.eigenvalues j)) := by sorry
