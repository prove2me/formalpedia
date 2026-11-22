-- Prove2me | Theorems.Thm_Auto_HeatData_continuous_w
-- name    : Auto.HeatData.continuous_w
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:15.164677+00:00
-- url     : https://prove2.me/theorems/c3af0039-30df-4e0f-9491-5b0f594f4ee9
-- title:
--   Heat Data: continuous w
-- statement:
--   The Heat Data construction uses the continuous w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4596-L4603
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4596-L4603

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
open Auto.HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
omit [Fintype ι] [DecidableEq ι]

theorem Auto.HeatData.continuous_w (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k) (k : Fin 3)
    (i : ι) :
    Continuous fun x => Hd.w (p x) (σ x) k i := by sorry
