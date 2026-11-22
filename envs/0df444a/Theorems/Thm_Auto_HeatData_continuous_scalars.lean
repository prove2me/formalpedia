-- Prove2me | Theorems.Thm_Auto_HeatData_continuous_scalars
-- name    : Auto.HeatData.continuous_scalars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:23.209868+00:00
-- url     : https://prove2.me/theorems/36ad70e4-4680-4d53-9f84-a7a3b88d5472
-- title:
--   Heat Data: continuous scalars
-- statement:
--   The Heat Data construction uses the continuous scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4707-L4729
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4707-L4729

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
open Auto.HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}

theorem Auto.HeatData.continuous_scalars (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    Continuous (fun x => Hd.e (p x) (σ x) η v) ∧ Continuous (fun x => tr32 η (Hd.T (p x) (σ x)
      v) (Hd.Ui (p x) (σ x) v)) ∧ Continuous (fun x => tr32 η (Hd.T (p x) (σ x) v) (wGram (Hd.Brow
      (p x) (σ x) v) (Hd.ddw (p x) (σ x) v))) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v)
      (Hd.Pnext (p x) (σ x) v)) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v) (Hd.Pprev (p x)
      (σ x) v)) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v) (wGram (Hd.Bnext (p x) (σ x) v)
      (Hd.ddw (p x) (σ x) (v + 1)))) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v) (wGram
      (Hd.Bprev (p x) (σ x) v) (Hd.ddw (p x) (σ x) (v - 1)))) ∧ Continuous (fun x => Hd.V (p x) (σ
      x) η v) ∧ Continuous (fun x => Hd.Ynext (p x) (σ x) η v) ∧ Continuous (fun x => Hd.Yprev (p
      x) (σ x) η v) ∧ Continuous (fun x => Hd.Z (p x) (σ x) η v) := by sorry
