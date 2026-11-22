-- Prove2me | Theorems.Thm_Auto_blk3_conjTranspose
-- name    : Auto.blk3_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:12.891145+00:00
-- url     : https://prove2.me/theorems/4f34fe72-ed35-4b55-97f7-944c26a1a267
-- title:
--   Auto: blk3 conj Transpose
-- statement:
--   The Auto construction uses the blk3 conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2466-L2469
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2466-L2469

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
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] [Fintype ι]

theorem Auto.blk3_conjTranspose (a b c d e f g h i : Matrix ι ι ℂ) :
    (blk3 !![a, b, c; d, e, f; g, h, i])ᴴ = blk3 !![aᴴ, dᴴ, gᴴ; bᴴ, eᴴ, hᴴ; cᴴ, fᴴ, iᴴ] := by sorry
