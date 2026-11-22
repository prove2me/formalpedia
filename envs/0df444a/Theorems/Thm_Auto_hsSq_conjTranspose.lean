-- Prove2me | Theorems.Thm_Auto_hsSq_conjTranspose
-- name    : Auto.hsSq_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:58.753726+00:00
-- url     : https://prove2.me/theorems/ac559783-b723-42b0-b76e-0044dd58892d
-- title:
--   Auto: hs Sq conj Transpose
-- statement:
--   The Auto construction uses the hs Sq conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5647-L5649
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5647-L5649

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section

theorem Auto.hsSq_conjTranspose {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    hsSq Aᴴ = hsSq A := by sorry
