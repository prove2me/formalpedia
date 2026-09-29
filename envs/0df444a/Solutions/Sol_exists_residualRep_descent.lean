-- Prove2me | solution 1 for exists_residualRep_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/754701f3-8753-5128-bec3-f0eb55661f88

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_residualRep_descent
set_option autoImplicit false

namespace T10DescSol

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k)

private noncomputable def matAux (b : Module.Basis (Fin 2) k ρbar.V) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k where
  toFun σ := LinearMap.toMatrix b b (ρbar.ρ σ)
  map_one' := by
    show LinearMap.toMatrix b b (ρbar.ρ 1) = 1
    rw [map_one]
    exact LinearMap.toMatrix_id b
  map_mul' σ τ := by
    show LinearMap.toMatrix b b (ρbar.ρ (σ * τ))
        = LinearMap.toMatrix b b (ρbar.ρ σ) * LinearMap.toMatrix b b (ρbar.ρ τ)
    rw [map_mul]
    exact LinearMap.toMatrix_mul b _ _

set_option maxHeartbeats 3200000 in

private noncomputable def liftAuxU (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [Normal ℚ (↥L₀)] (b : Module.Basis (Fin 2) k ρbar.V)
    (hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)))
    (hker_le : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)).ker
      ≤ (matAux ρbar b).toHomUnits.ker) :
    ((↥L₀) ≃ₐ[ℚ] (↥L₀)) →* (Matrix (Fin 2) (Fin 2) k)ˣ :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
    (↥L₀)).liftOfSurjective hsurj ⟨(matAux ρbar b).toHomUnits, hker_le⟩

set_option maxHeartbeats 3200000 in
private theorem liftAuxU_spec (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [Normal ℚ (↥L₀)] (b : Module.Basis (Fin 2) k ρbar.V)
    (hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)))
    (hker_le : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)).ker
      ≤ (matAux ρbar b).toHomUnits.ker) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    liftAuxU ρbar L₀ b hsurj hker_le (AlgEquiv.restrictNormalHom (↥L₀) σ)
      = (matAux ρbar b).toHomUnits σ :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
    (↥L₀)).liftOfRightInverse_comp_apply _ _ ⟨(matAux ρbar b).toHomUnits, hker_le⟩ σ

end T10DescSol

open T10DescSol in
set_option maxHeartbeats 3200000 in
theorem solution {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀]
    [NumberField L₀] [IsGalois ℚ L₀]
    (hker : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L₀, σ x = x) → ρbar.ρ σ = 1)
    (b : Module.Basis (Fin 2) k ρbar.V) :
    ∃ ρmat : TaylorWiles.ResidualRep (↥L₀) k,
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ)
          = LinearMap.toMatrix b b (ρbar.ρ σ) := by
  classical
  haveI hnorm : Normal ℚ (↥L₀) := IsGalois.to_normal
  have hker_le : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)).ker
      ≤ (matAux ρbar b).toHomUnits.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    have h1 : ∀ x ∈ L₀, σ x = x := by
      intro x hx
      have h2 := @AlgEquiv.restrictNormalHom_apply ℚ _ (AlgebraicClosure ℚ) _ _ L₀ hnorm σ ⟨x, hx⟩
      have h4 := congrArg Subtype.val (AlgEquiv.ext_iff.mp hσ ⟨x, hx⟩)
      exact h2.symm.trans h4
    refine Units.ext ?_
    show LinearMap.toMatrix b b (ρbar.ρ σ) = 1
    rw [hker σ h1]
    exact LinearMap.toMatrix_id b
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI hnormQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (↥L₀)) :=
    AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)
  refine ⟨(Units.coeHom (Matrix (Fin 2) (Fin 2) k)).comp (liftAuxU ρbar L₀ b hsurj hker_le),
    fun σ => ?_⟩
  show (↑(liftAuxU ρbar L₀ b hsurj hker_le (AlgEquiv.restrictNormalHom (↥L₀) σ)) :
      Matrix (Fin 2) (Fin 2) k) = LinearMap.toMatrix b b (ρbar.ρ σ)
  exact congrArg Units.val (liftAuxU_spec ρbar L₀ b hsurj hker_le σ)

#print axioms solution

end S_exists_residualRep_descent
end P2MW
export P2MW.S_exists_residualRep_descent (solution)
