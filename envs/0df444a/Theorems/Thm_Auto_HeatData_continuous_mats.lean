-- Prove2me | Theorems.Thm_Auto_HeatData_continuous_mats
-- name    : Auto.HeatData.continuous_mats
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:59.94453+00:00
-- url     : https://prove2.me/theorems/193c929a-6d2f-4915-8599-e288609aca31
-- title:
--   Heat Data: continuous mats
-- statement:
--   The Heat Data construction uses the continuous mats property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4625-L4655
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4625-L4655

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

theorem Auto.HeatData.continuous_mats (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (v : Fin 3) :
    Continuous (fun x => Hd.T (p x) (σ x) v) ∧ Continuous (fun x => Hd.S (p x) (σ x) v) ∧
      Continuous (fun x => Hd.Ui (p x) (σ x) v) ∧ Continuous (fun x => Hd.Pnext (p x) (σ x) v) ∧
      Continuous (fun x => Hd.Pprev (p x) (σ x) v) ∧ Continuous (fun x => wGram (Hd.Brow (p x) (σ
      x) v) (Hd.ddw (p x) (σ x) v)) ∧ Continuous (fun x => wGram (Hd.Bnext (p x) (σ x) v) (Hd.ddw
      (p x) (σ x) (v + 1))) ∧ Continuous (fun x => wGram (Hd.Bprev (p x) (σ x) v) (Hd.ddw (p x) (σ
      x) (v - 1))) := by sorry
