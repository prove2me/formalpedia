-- Prove2me | Theorems.Thm_Auto_HeatData_vertex_avg
-- name    : Auto.HeatData.vertex_avg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:38.600634+00:00
-- url     : https://prove2.me/theorems/26f4047f-9f7e-4786-aa82-b5ea060652b4
-- title:
--   Heat Data: vertex avg
-- statement:
--   The Heat Data construction uses the vertex avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6507-L6636
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6507-L6636

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)

theorem Auto.HeatData.vertex_avg (hh : 0 < Hd.h) (v : Fin 3) {j : ℕ} (hj : 1 ≤ j) {Ca : ℝ}
    (hCa : ∀ s, 0 < s → ∀ d, |acoef j s d| ≤ Ca * √s) (p : Fin 3 → ℝ) {s : ℝ} (hs : 0 < s) :
    matCost (Hd.T p (fun _ => 11 / 10 * s) v) ((Hd.R p (fun _ => 11 / 10 * s) v)ᴴ * rdiag (fun i
      => Dfun j s (Hd.u i - p v)) * Hd.R p (fun _ => 11 / 10 * s) v) ≤ ENNReal.ofReal (Ca ^ 2 * s)
      * ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) * matCost (Hd.T (Function.update p v (p v +
      d)) (Function.update (fun _ => 11 / 10 * s) v s) v) (Hd.Ui (Function.update p v (p v + d))
      (Function.update (fun _ => 11 / 10 * s) v s) v) := by sorry
