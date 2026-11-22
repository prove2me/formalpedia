-- Prove2me | Theorems.Thm_Auto_HeatData_e_mixed
-- name    : Auto.HeatData.e_mixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:11.392489+00:00
-- url     : https://prove2.me/theorems/c35866f5-511f-4303-9ced-7f5baa8f938f
-- title:
--   Heat Data: e mixed
-- statement:
--   The Heat Data construction uses the e mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3407-L3437
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3407-L3437

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

theorem Auto.HeatData.e_mixed (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v + 1) q) σ v) (Hd.Pprev
      (Function.update p (v + 1) q) σ v)) (Hd.Z p σ η v) (p (v + 1)) := by sorry
