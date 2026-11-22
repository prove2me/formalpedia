-- Prove2me | Theorems.Thm_Auto_hasDerivAt_energy_hessian
-- name    : Auto.hasDerivAt_energy_hessian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:51.667804+00:00
-- url     : https://prove2.me/theorems/be1c18e5-6cb0-4d01-bd7f-4da173f63c3a
-- title:
--   Auto: has Deriv At energy hessian
-- statement:
--   The Auto construction uses the has Deriv At energy hessian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1530-L1548
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1530-L1548

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

theorem Auto.hasDerivAt_energy_hessian {P G : ℝ → Matrix n n ℂ} {P' G' : Matrix n n ℂ} {θ₀ η : ℝ}
    (hη : 0 < η) (hP : ∀ θ, (P θ).PosSemidef)
    (hd : ∀ i j, HasDerivAt (fun θ => P θ i j) (P' i j) θ₀)
    (hG : ∀ i j, HasDerivAt (fun θ => G θ i j) (G' i j) θ₀) (hGH : (G θ₀).IsHermitian) :
    HasDerivAt (fun θ => (3 / 2) * ((CFC.sqrt (P θ + (η : ℂ) • 1) * G θ).trace).re) (matCostBil
      (P θ₀ + (η : ℂ) • 1) P' (G θ₀) + (3 / 2) * ((CFC.sqrt (P θ₀ + (η : ℂ) • 1) * G').trace).re)
      θ₀ := by sorry
