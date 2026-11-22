-- Prove2me | Theorems.Thm_Auto_HeatData_hasDerivAt_e_curve
-- name    : Auto.HeatData.hasDerivAt_e_curve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:17.735531+00:00
-- url     : https://prove2.me/theorems/dad8601a-1991-44f0-9e62-912728cc0ec6
-- title:
--   Heat Data: has Deriv At e curve
-- statement:
--   The Heat Data construction uses the has Deriv At e curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3743-L3781
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3743-L3781

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

theorem Auto.HeatData.hasDerivAt_e_curve (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {c : ℝ → Fin 3 → ℝ}
    {c' : Fin 3 → ℝ} {θ₀ : ℝ} (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀)
    (hσ : ∀ k, 0 < c θ₀ k) (v : Fin 3) :
    HasDerivAt (fun θ => Hd.e p (c θ) η v) (c' v * tr32 η (Hd.T p (c θ₀) v) (Hd.Mrow p (c θ₀) v)
      + c' (v + 1) * tr32 η (Hd.T p (c θ₀) v) (Hd.Mnext p (c θ₀) v) + c' (v - 1) * tr32 η (Hd.T p
      (c θ₀) v) (Hd.Mprev p (c θ₀) v)) θ₀ := by sorry
