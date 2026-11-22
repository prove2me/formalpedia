-- Prove2me | Theorems.Thm_Auto_HeatData_entry_bounds
-- name    : Auto.HeatData.entry_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:20.530209+00:00
-- url     : https://prove2.me/theorems/2ba1047d-75d0-4389-84cf-f39cf224d1d6
-- title:
--   Heat Data: entry bounds
-- statement:
--   The Heat Data construction uses the entry bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4218-L4311
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4218-L4311

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
variable (Hd : HeatData ι)

theorem Auto.HeatData.entry_bounds (hh : 0 ≤ Hd.h) {σa σb : ℝ} (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ v, (∀ a b, ‖Hd.T p σ v a
      b‖ ≤ C * phi σb v p ^ 2 ∧ ‖Hd.Ui p σ v a b‖ ≤ C * phi σb v p ^ 2 ∧ ‖wGram (Hd.Brow p σ v)
      (Hd.ddw p σ v) a b‖ ≤ C * phi σb v p ^ 2) ∧ (∀ i j, ‖Hd.S p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧
      ‖Hd.Pnext p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧ ‖Hd.Pprev p σ v i j‖ ≤ C * phi σb v p ^ 2 ∧
      ‖wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)) i j‖ ≤ C * phi σb v p ^ 2 ∧ ‖wGram (Hd.Bprev p
      σ v) (Hd.ddw p σ (v - 1)) i j‖ ≤ C * phi σb v p ^ 2) := by sorry
