-- Prove2me | Theorems.Thm_Auto_continuous_wGram
-- name    : Auto.continuous_wGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:57.340297+00:00
-- url     : https://prove2.me/theorems/b8b213eb-3256-4a65-ba25-2f444b3b918c
-- title:
--   Auto: continuous w Gram
-- statement:
--   The Auto construction uses the continuous w Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4581-L4584
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4581-L4584

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]

theorem Auto.continuous_wGram {κ : Type*} {B : X → Matrix ι κ ℂ} {f : X → ι → ℝ} (hB : Continuous B)
    (hf : ∀ i, Continuous fun x => f x i) :
    Continuous fun x => wGram (B x) (f x) := by sorry
