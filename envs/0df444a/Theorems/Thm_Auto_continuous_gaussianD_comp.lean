-- Prove2me | Theorems.Thm_Auto_continuous_gaussianD_comp
-- name    : Auto.continuous_gaussianD_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:38.426322+00:00
-- url     : https://prove2.me/theorems/8b16cc5b-7826-48ea-8367-926f61e4892d
-- title:
--   Auto: continuous gaussian D comp
-- statement:
--   The Auto construction uses the continuous gaussian D comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4571-L4574
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4571-L4574

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

theorem Auto.continuous_gaussianD_comp (j : ℕ) {σ t : X → ℝ} (hσ : Continuous σ) (ht : Continuous t)
    (hpos : ∀ x, 0 < σ x) :
    Continuous (fun x => gaussianD j (σ x) (t x)) := by sorry
