-- Prove2me | Theorems.Thm_Auto_rdiag_posSemidef
-- name    : Auto.rdiag_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:45.247306+00:00
-- url     : https://prove2.me/theorems/5f2ac48f-3a79-406b-8d43-ec84a466c555
-- title:
--   Auto: rdiag pos Semidef
-- statement:
--   The Auto construction uses the rdiag pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2944-L2946
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2944-L2946

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [Fintype κ] [DecidableEq κ] [Fintype ι]

theorem Auto.rdiag_posSemidef {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : (rdiag f).PosSemidef := by sorry
