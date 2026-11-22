-- Prove2me | Theorems.Thm_Auto_continuousOn_Gm
-- name    : Auto.continuousOn_Gm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:49.72988+00:00
-- url     : https://prove2.me/theorems/9b44ab14-f533-4db4-9e78-3e56ae2ab7ba
-- title:
--   Auto: continuous On Gm
-- statement:
--   The Auto construction uses the continuous On Gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4858-L4862
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4858-L4862

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.continuousOn_Gm (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Gm β m z.1 z.2) (Set.Ioi 0 ×ˢ Set.univ) := by sorry
