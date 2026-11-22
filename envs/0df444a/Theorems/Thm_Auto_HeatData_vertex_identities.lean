-- Prove2me | Theorems.Thm_Auto_HeatData_vertex_identities
-- name    : Auto.HeatData.vertex_identities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:55.850353+00:00
-- url     : https://prove2.me/theorems/25d3c0af-4559-4538-b6f6-77d7db4a86e8
-- title:
--   Heat Data: vertex identities
-- statement:
--   The Heat Data construction uses the vertex identities property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5066-L5118
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5066-L5118

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
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)

theorem Auto.HeatData.vertex_identities (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2)
    {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) (hab : sa ≤ sb) {s : ℝ} (hs : s ∈ Set.Icc sa sb) :
    ∫ p, Gm β 0 s p * (Hd.qV α η v + Hd.qA α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p,
      Gm β 0 s p * (Hd.qYn α η v + Hd.qB α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p, Gm
      β 0 s p * (Hd.qYp α η v + Hd.qC α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p, Gm β 0
      s p * Hd.qZ α η v s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p := by sorry
