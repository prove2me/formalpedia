-- Prove2me | Theorems.Thm_Auto_sqrt_eq_conj_diagonal
-- name    : Auto.sqrt_eq_conj_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:19.902249+00:00
-- url     : https://prove2.me/theorems/d4373ab8-eb50-4cfb-8cb0-5ab8ec17a83b
-- title:
--   Auto: sqrt eq conj diagonal
-- statement:
--   The Auto construction uses the sqrt eq conj diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L820-L825
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L820-L825

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

theorem Auto.sqrt_eq_conj_diagonal {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    CFC.sqrt P = (hP.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((√(hP.1.eigenvalues i) : ℝ) : ℂ)) * star (hP.1.eigenvectorUnitary : Matrix n n ℂ) := by sorry
