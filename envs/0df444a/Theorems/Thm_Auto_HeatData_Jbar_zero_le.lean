-- Prove2me | Theorems.Thm_Auto_HeatData_Jbar_zero_le
-- name    : Auto.HeatData.Jbar_zero_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:23.170392+00:00
-- url     : https://prove2.me/theorems/e3cff7fd-2980-4e3e-9168-f863e96f2076
-- title:
--   Heat Data: Jbar zero le
-- statement:
--   The Heat Data construction uses the Jbar zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5769-L5843
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5769-L5843

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

theorem Auto.HeatData.Jbar_zero_le (hh : 0 < Hd.h) (kk : ι → ℤ) (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (α : Fin 3 → ℝ) (hα : ∀ k, 1 ≤ α k) {s : ℝ}
    (hs : Hd.h ^ 2 ≤ s) :
    Hd.Jbar α 0 s ≤ 2 * √2 * (1 + √(2 / π)) * ∑ v, Hd.nCube v := by sorry
