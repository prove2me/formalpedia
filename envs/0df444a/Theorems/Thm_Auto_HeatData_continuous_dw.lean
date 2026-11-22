-- Prove2me | Theorems.Thm_Auto_HeatData_continuous_dw
-- name    : Auto.HeatData.continuous_dw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:07.936539+00:00
-- url     : https://prove2.me/theorems/23f9b5c4-3850-4232-8190-e62f95ca96b8
-- title:
--   Heat Data: continuous dw
-- statement:
--   The Heat Data construction uses the continuous dw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4606-L4610
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4606-L4610

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

theorem Auto.HeatData.continuous_dw (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (k : Fin 3) (i : ι) :
    Continuous fun x => Hd.dw (p x) (σ x) k i := by sorry
