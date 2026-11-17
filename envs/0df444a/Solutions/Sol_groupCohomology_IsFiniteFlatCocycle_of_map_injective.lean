-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatCocycle.of_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:46.758118+00:00
-- url     : https://prove2.me/submissions/8bbbc36e-a6fb-4ce1-b393-daaedb806f84

import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_subobject
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false

namespace groupCohomology

/-- An admissible coefficient-image cocycle has an admissible lift through an
injective equivariant coefficient map. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup U] [Module (ZMod p) U]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (τ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U)
    (c : cocycles₁ (Rep.of ρ)) (d : cocycles₁ (Rep.of τ))
    (i : W →ₗ[ZMod p] U) (hi : Function.Injective i)
    (hiact : ∀ σ w, i (ρ σ w) = τ σ (i w))
    (hic : ∀ σ, i (c σ) = d σ)
    (hd : IsFiniteFlatCocycle p τ d) : IsFiniteFlatCocycle p ρ c := by
  letI := cocycleExtensionAction p ρ c
  letI := cocycleExtensionAction p τ d
  let I : (W × ZMod p) →+ (U × ZMod p) :=
    { toFun := fun x => (i x.1, x.2)
      map_zero' := by simp
      map_add' := by intro x y; ext <;> simp }
  apply IsFiniteFlatRepresentation.subobject p hd I
  · intro x y h
    exact Prod.ext (hi (congrArg (fun z : U × ZMod p => z.1) h))
      (congrArg (fun z : U × ZMod p => z.2) h)
  · intro σ x
    apply Prod.ext
    · change i (ρ σ x.1 + x.2 • c σ) = τ σ (i x.1) + x.2 • d σ
      rw [map_add, map_smul, hiact, hic]
    · rfl

end groupCohomology
