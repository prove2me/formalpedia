-- Prove2me | Theorems.Thm_Auto_HeatData_continuous_ddw
-- name    : Auto.HeatData.continuous_ddw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:29.997597+00:00
-- url     : https://prove2.me/theorems/4472ac63-e380-4594-ac36-742e28bae247
-- title:
--   Heat Data: continuous ddw
-- statement:
--   The Heat Data construction uses the continuous ddw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4613-L4617
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4613-L4617

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

theorem Auto.HeatData.continuous_ddw (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (k : Fin 3) (i : ι) :
    Continuous fun x => Hd.ddw (p x) (σ x) k i := by sorry
