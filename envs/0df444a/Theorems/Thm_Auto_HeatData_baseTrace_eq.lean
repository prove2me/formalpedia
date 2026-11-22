-- Prove2me | Theorems.Thm_Auto_HeatData_baseTrace_eq
-- name    : Auto.HeatData.baseTrace_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:54.770807+00:00
-- url     : https://prove2.me/theorems/0e8be456-75c9-4444-a94b-7d85c4428870
-- title:
--   Heat Data: base Trace eq
-- statement:
--   The Heat Data construction uses the base Trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6729-L6756
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6729-L6756

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

theorem Auto.HeatData.baseTrace_eq (hh : 0 ≤ Hd.h) {m : ℕ} (hm : m = 3 ∨ m = 4) {s : ℝ} (hs : 0 < s)
    (p : Fin 3 → ℝ) :
    Hd.baseTrace m p s = ((Hd.h ^ 3 * √s ^ m : ℝ) : ℂ) * ∑ i, ∑ j, ∑ k, Hd.A 0 i j * Hd.A 1 j k
      * Hd.A 2 k i * ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0) * gaussianD (dexp m 1)
      (21 / 20 * s) (Hd.u j - p 1) * gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2) : ℝ) : ℂ) := by sorry
