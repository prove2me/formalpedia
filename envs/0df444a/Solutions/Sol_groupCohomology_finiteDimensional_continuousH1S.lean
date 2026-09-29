-- Prove2me | solution 1 for groupCohomology.finiteDimensional_continuousH1S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a1738a70-eca6-5522-a546-511443128542

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

import Theorems.Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_continuousH1S

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 3200000

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m) :
    FiniteDimensional (ZMod p) (continuousH1S S M) := by
  classical
  have hp : p.Prime := Fact.out

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

  let U₀ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := M.ρ.ker
  have hU₀open : IsOpen (U₀ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    obtain ⟨F₁, hF₁, hF₁U⟩ : ∃ F₁ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₁ ∧
        F₁.fixingSubgroup ≤ U₀ := by
      let bM := Module.finBasis (ZMod p) M
      choose F hF hFfix using fun i => hsm (bM i)
      refine ⟨⨆ i, F i, ?_, fun s hs => ?_⟩
      · haveI := fun i => hF i
        exact IntermediateField.finiteDimensional_iSup_of_finite
      · show M.ρ s = 1
        refine bM.ext fun i => ?_
        exact hFfix i s (IntermediateField.fixingSubgroup_antitone (le_iSup F i) hs)
    haveI := hF₁
    exact Subgroup.isOpen_mono hF₁U F₁.fixingSubgroup_isOpen
  have hU₀closed : IsClosed (U₀ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := U₀.isClosed_of_isOpen hU₀open
  let F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField U₀
  have hF₀K : F₀.fixingSubgroup = U₀ := InfiniteGalois.fixingSubgroup_fixedField ⟨U₀, hU₀closed⟩
  have hF₀fd : FiniteDimensional ℚ F₀ := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    show IsOpen (F₀.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    rw [hF₀K]; exact hU₀open
  haveI := hF₀fd
  haveI : NumberField F₀ := @NumberField.mk _ _ inferInstance hF₀fd

  obtain ⟨L, hLfd, -, hL⟩ := AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside F₀ p hp
    (S.image (fun q : Nat.Primes => (q : ℕ)))
  haveI := hLfd
  let U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := L.fixingSubgroup
  haveI : U.FiniteIndex := ⟨by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'⟩
  haveI : Finite M := Module.finite_of_finite (ZMod p)
  let bM := Module.finBasis (ZMod p) M
  have hcmul : ∀ (c : cocycles₁ M) g h, c (g * h) = M.ρ g (c h) + c g := fun c => (mem_cocycles₁_iff (⇑c)).1 c.2

  have hvan : ∀ (c : levelCocyclesS₁ S M) (u : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), u ∈ U →
      (c : cocycles₁ M) u = 0 := by
    intro c u hu
    obtain ⟨Fc, hFc, hcF⟩ := (mem_levelCochainsS₁_iff S M _).1 c.2
    have hcF' : ∀ g t, t ∈ Fc.fixingSubgroup → (c : cocycles₁ M) (g * t) = (c : cocycles₁ M) g := hcF
    haveI := hFc.1
    have hczero : ∀ t, t ∈ Fc.fixingSubgroup → (c : cocycles₁ M) t = 0 := by
      intro t ht
      rw [← one_mul t, hcF' 1 t ht]
      exact cocycles₁_map_one _
    refine bM.ext_elem fun i => ?_
    rw [map_zero]
    refine hL (fun g => bM.coord i ((c : cocycles₁ M) g)) ?_ ?_ ?_ u hu
    · intro σ τ hσ _
      show bM.coord i ((c : cocycles₁ M) (σ * τ)) = bM.coord i ((c : cocycles₁ M) σ) + bM.coord i ((c : cocycles₁ M) τ)
      have hσ1 : M.ρ σ = 1 := by
        have : σ ∈ U₀ := by rw [← hF₀K]; exact hσ
        exact this
      rw [hcmul, hσ1, Module.End.one_apply, map_add, add_comm]
    · refine ⟨F₀ ⊔ Fc, IntermediateField.finiteDimensional_sup F₀ Fc, fun σ hσ => ?_⟩
      show bM.coord i ((c : cocycles₁ M) σ) = 0
      rw [hczero σ (IntermediateField.fixingSubgroup_antitone le_sup_right hσ), map_zero]
    · intro q hq hqS P hP σ hσI _
      have hq' : (⟨q, hq⟩ : Nat.Primes) ∉ S := fun h => hqS (Finset.mem_image.2 ⟨_, h, rfl⟩)
      show bM.coord i ((c : cocycles₁ M) σ) = 0
      rw [hczero σ (hFc.2 ⟨q, hq⟩ hq' P hP hσI), map_zero]

  let Ψ : levelCocyclesS₁ S M → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ U) → M :=
    fun c x => (c : cocycles₁ M) x.out
  have hΨ : Function.Injective Ψ := by
    intro c c' h
    apply Subtype.ext
    apply cocycles₁_ext
    intro g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
    have hg : g = (QuotientGroup.mk g : _ ⧸ U).out * ((u⁻¹ : U) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
      rw [hu, Subgroup.coe_inv, mul_inv_cancel_right]
    have h1 := congrFun h (QuotientGroup.mk g)
    rw [hg, hcmul (c : cocycles₁ M), hcmul (c' : cocycles₁ M), hvan c _ (u⁻¹).2, hvan c' _ (u⁻¹).2]
    exact congrArg _ h1
  haveI : Finite (levelCocyclesS₁ S M) := Finite.of_injective Ψ hΨ
  haveI : Module.Finite (ZMod p) (levelCocyclesS₁ S M) := Module.Finite.of_finite
  show Module.Finite (ZMod p) ((levelCocyclesS₁ S M).map (H1π M).hom)
  infer_instance

end S_groupCohomology_finiteDimensional_continuousH1S
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_continuousH1S (solution)
