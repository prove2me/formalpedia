-- Prove2me | solution 1 for groupCohomology.IsFiniteFlatCocycle.of_map_add_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:46.116103+00:00
-- url     : https://prove2.me/submissions/100f5fc1-4212-4e58-a647-0adad1f1f7df

import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_subobject
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false

namespace groupCohomology

/-- The inverse-image property for admissible classes. The equality of cohomology
classes is expressed by the displayed coboundary, with convention `σ b - b`.
The induced subobject map is `(v,t) ↦ (i v - t • b,t)`. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup U] [Module (ZMod p) U]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (τ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U)
    (c : cocycles₁ (Rep.of ρ)) (d : cocycles₁ (Rep.of τ))
    (i : W →ₗ[ZMod p] U) (hi : Function.Injective i)
    (hiact : ∀ σ w, i (ρ σ w) = τ σ (i w))
    (b : U) (hic : ∀ σ, d σ = i (c σ) + (τ σ b - b))
    (hd : IsFiniteFlatCocycle p τ d) : IsFiniteFlatCocycle p ρ c := by
  letI := cocycleExtensionAction p ρ c
  letI := cocycleExtensionAction p τ d
  let I : (W × ZMod p) →+ (U × ZMod p) :=
    { toFun := fun x => (i x.1 - x.2 • b, x.2)
      map_zero' := by simp
      map_add' := by
        intro x y
        ext
        · change i (x.1 + y.1) - (x.2 + y.2) • b =
            (i x.1 - x.2 • b) + (i y.1 - y.2 • b)
          rw [map_add, add_smul]
          abel
        · rfl }
  apply IsFiniteFlatRepresentation.subobject p hd I
  · intro x y h
    have hs : x.2 = y.2 := congrArg (fun z : U × ZMod p => z.2) h
    apply Prod.ext _ hs
    apply hi
    have hf : i x.1 - x.2 • b = i y.1 - y.2 • b := congrArg (fun z : U × ZMod p => z.1) h
    rw [hs] at hf
    have hadd := congrArg (fun z : U => z + y.2 • b) hf
    simpa only [sub_add_cancel] using hadd
  · intro σ x
    apply Prod.ext
    · change i (ρ σ x.1 + x.2 • c σ) - x.2 • b =
        τ σ (i x.1 - x.2 • b) + x.2 • d σ
      rw [map_add, map_smul, hiact, hic]
      simp only [map_sub, map_smul, smul_add, smul_sub]
      abel
    · rfl

end groupCohomology
