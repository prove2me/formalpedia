-- Prove2me | Theorems.Thm_Auto_HeatData_continuousOn_family
-- name    : Auto.HeatData.continuousOn_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:57.981145+00:00
-- url     : https://prove2.me/theorems/e35eebc4-9455-43dd-b0b4-b9b50bb0b6db
-- title:
--   Heat Data: continuous On family
-- statement:
--   The Heat Data construction uses the continuous On family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4937-L4966
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4937-L4966

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
open Auto.HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ)

theorem Auto.HeatData.continuousOn_family (hα : ∀ k, 0 < α k) {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    let S : Set (ℝ × (Fin 3 → ℝ)) := Set.Ioi 0 ×ˢ Set.univ
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.e z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) =>
      tr32 η (Hd.T z.2 (sig α z.1) v) (Hd.Ui z.2 (sig α z.1) v)) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => tr32 η (Hd.T z.2 (sig α z.1) v) (wGram (Hd.Brow z.2
        (sig α z.1) v) (Hd.ddw z.2 (sig α z.1) v))) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) =>
      tr32 η (Hd.S z.2 (sig α z.1) v) (Hd.Pnext z.2 (sig α z.1) v)) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) =>
      tr32 η (Hd.S z.2 (sig α z.1) v) (Hd.Pprev z.2 (sig α z.1) v)) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => tr32 η (Hd.S z.2 (sig α z.1) v) (wGram (Hd.Bnext z.2
        (sig α z.1) v) (Hd.ddw z.2 (sig α z.1) (v + 1)))) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => tr32 η (Hd.S z.2 (sig α z.1) v) (wGram (Hd.Bprev z.2
        (sig α z.1) v) (Hd.ddw z.2 (sig α z.1) (v - 1)))) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.V z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.Ynext z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.Yprev z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.Z z.2 (sig α z.1) η v) S := by sorry
