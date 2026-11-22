-- Prove2me | Theorems.Thm_Auto_HeatData_hasDerivAt_sqw_curve
-- name    : Auto.HeatData.hasDerivAt_sqw_curve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:23.739987+00:00
-- url     : https://prove2.me/theorems/5fd2e360-1764-4468-839e-c260c57dcaba
-- title:
--   Heat Data: has Deriv At sqw curve
-- statement:
--   The Heat Data construction uses the has Deriv At sqw curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3735-L3741
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3735-L3741

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
omit [DecidableEq ι] [Fintype ι]

theorem Auto.HeatData.hasDerivAt_sqw_curve (hh : 0 < Hd.h) {c : ℝ → Fin 3 → ℝ} {c' : Fin 3 → ℝ} {θ₀ : ℝ}
    (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀) (hσ : ∀ k, 0 < c θ₀ k) (k : Fin 3) (i : ι) :
    HasDerivAt (fun θ => Hd.sqw p (c θ) k i) (c' k * Hd.dsq p (c θ₀) k i) θ₀ := by sorry
