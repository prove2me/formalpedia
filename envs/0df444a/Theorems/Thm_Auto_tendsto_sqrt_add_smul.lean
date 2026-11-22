-- Prove2me | Theorems.Thm_Auto_tendsto_sqrt_add_smul
-- name    : Auto.tendsto_sqrt_add_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:40.229798+00:00
-- url     : https://prove2.me/theorems/45007b34-c195-4441-8652-71f33ecb3ee3
-- title:
--   Auto: tendsto sqrt add smul
-- statement:
--   The Auto construction uses the tendsto sqrt add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5949-L5962
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5949-L5962

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
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.tendsto_sqrt_add_smul {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℕ → ℝ}
    (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => CFC.sqrt (P + (η m : ℂ) • 1)) atTop (𝓝 (CFC.sqrt P)) := by sorry
