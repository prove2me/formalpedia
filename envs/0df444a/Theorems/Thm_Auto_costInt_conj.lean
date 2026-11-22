-- Prove2me | Theorems.Thm_Auto_costInt_conj
-- name    : Auto.costInt_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:04.498779+00:00
-- url     : https://prove2.me/theorems/38773485-5912-46ae-b034-d7d8e71d4277
-- title:
--   Auto: cost Int conj
-- statement:
--   The Auto construction uses the cost Int conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L843-L869
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L843-L869

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

theorem Auto.costInt_conj (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ))
    (K X : Matrix n n ℂ) :
    costInt A K X = ∑ i, ∑ j, (2 * ((starRingEnd ℂ) ((star (U : Matrix n n ℂ) * K * (U : Matrix
      n n ℂ)) i j) * (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j).re - (a i + a j) *
      ‖(star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j‖ ^ 2) := by sorry
