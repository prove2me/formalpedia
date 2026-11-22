-- Prove2me | Theorems.Thm_Auto_HeatData_integral_baseTrace
-- name    : Auto.HeatData.integral_baseTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:53.991281+00:00
-- url     : https://prove2.me/theorems/21374ba5-3443-45c4-9caa-1ac2c9cf4f95
-- title:
--   Heat Data: integral base Trace
-- statement:
--   The Heat Data construction uses the integral base Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6758-L6805
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6758-L6805

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

theorem Auto.HeatData.integral_baseTrace (hh : 0 ≤ Hd.h) {m : ℕ} (hm : m = 3 ∨ m = 4) {s : ℝ} (hs : 0 < s) :
    Integrable (fun q : Fin 2 → ℝ => Hd.baseTrace m (planePt q) s) ∧ ∫ q : Fin 2 → ℝ,
      Hd.baseTrace m (planePt q) s = ((Hd.h ^ 3 * √s ^ m : ℝ) : ℂ) * ∑ i, ∑ j, ∑ k, Hd.A 0 i j *
      Hd.A 1 j k * Hd.A 2 k i * (gaussianD m (63 / 20 * s) (Hd.u i + Hd.u j + Hd.u k) : ℂ) := by sorry
