-- Prove2me | Theorems.Thm_Auto_matCost_eq_sum_of_conj
-- name    : Auto.matCost_eq_sum_of_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:14.860003+00:00
-- url     : https://prove2.me/theorems/1a5df26b-0c46-42a1-b0f4-c5459dc65f7a
-- title:
--   Auto: mat Cost eq sum of conj
-- statement:
--   The Auto construction uses the mat Cost eq sum of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L889-L1004
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L889-L1004

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

theorem Auto.matCost_eq_sum_of_conj {P : Matrix n n ℂ} (U : Matrix.unitaryGroup n ℂ) (p : n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hPU : P = (U : Matrix n n ℂ) * diagonal (fun i => ((p i : ℝ) : ℂ)) * star (U : Matrix n n
      ℂ)) (K : Matrix n n ℂ) :
    matCost P K = ∑ i, ∑ j, ENNReal.ofReal ((3 / 2) * ‖(star (U : Matrix n n ℂ) * K * (U :
      Matrix n n ℂ)) i j‖ ^ 2) / ENNReal.ofReal (√(p i) + √(p j)) := by sorry
