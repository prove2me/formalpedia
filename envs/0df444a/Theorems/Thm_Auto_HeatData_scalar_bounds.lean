-- Prove2me | Theorems.Thm_Auto_HeatData_scalar_bounds
-- name    : Auto.HeatData.scalar_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:57.461969+00:00
-- url     : https://prove2.me/theorems/dcab05ca-50df-4a6f-9882-2a8b57e19d91
-- title:
--   Heat Data: scalar bounds
-- statement:
--   The Heat Data construction uses the scalar bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4491-L4549
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4491-L4549

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

theorem Auto.HeatData.scalar_bounds (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) {σa σb : ℝ} (ha : 0 < σa)
    (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ v, |Hd.e p σ η v| ≤ C *
      phi σb v p ^ 2 ∧ |tr32 η (Hd.T p σ v) (Hd.Ui p σ v)| ≤ C * phi σb v p ^ 2 ∧ |tr32 η (Hd.T p
      σ v) (wGram (Hd.Brow p σ v) (Hd.ddw p σ v))| ≤ C * phi σb v p ^ 2 ∧ |tr32 η (Hd.S p σ v)
      (Hd.Pnext p σ v)| ≤ C * phi σb v p ^ 2 ∧ |tr32 η (Hd.S p σ v) (Hd.Pprev p σ v)| ≤ C * phi σb
      v p ^ 2 ∧ |tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)))| ≤ C * phi σb v
      p ^ 2 ∧ |tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (Hd.ddw p σ (v - 1)))| ≤ C * phi σb v p
      ^ 2 ∧ |Hd.V p σ η v| ≤ C * phi σb v p ^ 2 ∧ |Hd.Ynext p σ η v| ≤ C * phi σb v p ^ 2 ∧
      |Hd.Yprev p σ η v| ≤ C * phi σb v p ^ 2 ∧ |Hd.Z p σ η v| ≤ C * phi σb v p ^ 2 := by sorry
