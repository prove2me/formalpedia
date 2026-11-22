-- Prove2me | Theorems.Thm_Auto_continuous_slice
-- name    : Auto.continuous_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:51.310811+00:00
-- url     : https://prove2.me/theorems/fdd3c4b2-9554-41d2-96fe-bbff90767ddf
-- title:
--   Auto: continuous slice
-- statement:
--   The Auto construction uses the continuous slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4864-L4867
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4864-L4867

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

theorem Auto.continuous_slice {Q : ℝ × (Fin 3 → ℝ) → ℝ} (hQ : ContinuousOn Q (Set.Ioi 0 ×ˢ Set.univ))
    {s : ℝ} (hs : 0 < s) :
    Continuous fun p => Q (s, p) := by sorry
