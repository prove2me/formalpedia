-- Prove2me | solution 1 for relativeUnitsModule_zeta_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:10.985546+00:00
-- url     : https://prove2.me/submissions/b7dd0dd9-0af1-44a8-a4a4-0b0b449cc509

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
variable [IsGalois k K]
theorem _root_.solution (x) :
    (zeta p) • mkG x = mkG (Units.map (galRestrictHom (𝓞 k) k K (𝓞 K) σ) x) := by
  let φ := (addMonoidEndRingEquivInt _
      (monoidEndToAdditive _ <| relativeUnitsMap <| ((AlgEquiv.algHomUnitsEquiv _ _).symm σ).val))
  change QuotientAddGroup.mk ((Module.AEval'.of φ).symm <|
    Polynomial.X (R := ℤ) • Module.AEval'.of φ (Additive.ofMul (QuotientGroup.mk x))) = _
  simp only [Module.AEval.of_symm_smul, Polynomial.aeval_X,
    LinearEquiv.symm_apply_apply, Module.End.smul_def, unitToU]
  rfl
