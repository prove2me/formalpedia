-- Prove2me | Theorems.Thm_Auto_add_smul_one_eq_conj
-- name    : Auto.add_smul_one_eq_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:45.473114+00:00
-- url     : https://prove2.me/theorems/2b14a795-028d-46d2-abdb-ad2aaec7167d
-- title:
--   Auto: add smul one eq conj
-- statement:
--   The Auto construction uses the add smul one eq conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1343-L1352
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1343-L1352

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
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.add_smul_one_eq_conj {P : Matrix n n ℂ} (hP : P.IsHermitian) (c : ℝ) :
    P + (c : ℂ) • 1 = (hP.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((hP.eigenvalues i + c : ℝ) : ℂ)) * star (hP.eigenvectorUnitary : Matrix n n ℂ) := by sorry
