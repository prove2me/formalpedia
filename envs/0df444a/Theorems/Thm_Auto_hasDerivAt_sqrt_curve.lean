-- Prove2me | Theorems.Thm_Auto_hasDerivAt_sqrt_curve
-- name    : Auto.hasDerivAt_sqrt_curve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:26.277887+00:00
-- url     : https://prove2.me/theorems/6c4288ec-186d-4234-a7e4-e7ca6f740f85
-- title:
--   Auto: has Deriv At sqrt curve
-- statement:
--   The Auto construction uses the has Deriv At sqrt curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1231-L1319
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1231-L1319

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.hasDerivAt_sqrt_curve {Y : ℝ → Matrix n n ℂ} {Y' : Matrix n n ℂ} {θ₀ η : ℝ} (hη : 0 < η)
    (hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (Y' i j) θ₀) :
    ∀ i j, HasDerivAt (fun θ => CFC.sqrt (Y θ) i j) (sylvSol (CFC.sqrt (Y θ₀)) Y' i j) θ₀ := by sorry
