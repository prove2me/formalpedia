-- Prove2me | Theorems.Thm_Auto_hasDerivAt_energyReg
-- name    : Auto.hasDerivAt_energyReg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:59.082738+00:00
-- url     : https://prove2.me/theorems/4371957c-fbcc-4ba0-a01d-01d10d9a119b
-- title:
--   Auto: has Deriv At energy Reg
-- statement:
--   The Auto construction uses the has Deriv At energy Reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1405-L1437
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1405-L1437

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

theorem Auto.hasDerivAt_energyReg {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {θ₀ η : ℝ} (hη : 0 < η)
    (hP : ∀ θ, (P θ).PosSemidef) (hd : ∀ i j, HasDerivAt (fun θ => P θ i j) (P' i j) θ₀) :
    HasDerivAt (fun θ => energyReg η (P θ)) ((3 / 2) * ((CFC.sqrt (P θ₀ + (η : ℂ) • 1) *
      P').trace).re) θ₀ := by sorry
