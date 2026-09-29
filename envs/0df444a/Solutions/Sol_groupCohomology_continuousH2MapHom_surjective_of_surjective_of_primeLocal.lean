-- Prove2me | solution 1 for groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/08b8499f-b2bf-50d3-9a54-93bf72c0c492

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_Rep_exists_hom_coind_res_comp_eq_index_smul
import Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1
import Theorems.Thm_groupCohomology_deltaCochain1_mem_levelCoboundaries2_iff
import Theorems.Thm_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_deltaCochain1_mem_levelCocycles2
import Theorems.Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
import Theorems.Thm_Rep_exists_level_coind_apply_eq_self
import Theorems.Thm_Rep_exists_ker_trace_cyclicShift
import Theorems.Thm_Rep_exists_coind_map_ker_trace
import Theorems.Thm_Rep_shortExact_coind_ker_trace
import Theorems.Thm_Rep_exists_coind_inclusion_ker_trace
import Theorems.Thm_ExtCitation_comap_rootsOfUnity_levels_of_isOpen
import Theorems.Thm_groupCohomology_exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

namespace P2mS26HD2
open groupCohomology ExtCitation

noncomputable def T (q : Nat.Primes) (N : ℕ) : Subgroup (primeLocalGaloisGroup q) :=
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
      : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))

noncomputable def UN (q : Nat.Primes) (S : Subgroup (primeLocalGaloisGroup q)) (N : ℕ) : Subgroup S :=
  Subgroup.comap S.subtype (T q N)

universe w
variable {k Γ : Type w} [CommRing k] [Group Γ]

theorem pkg (U : Subgroup Γ) [U.Normal] [U.FiniteIndex] (φ : Γ)
    (hφ : ∀ g : Γ, ∃ (n : ℤ) (u : Γ), u ∈ U ∧ g = φ ^ n * u) (X : Rep.{w} k Γ) :
    ∃ (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
      (K : Rep.{w} k Γ) (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K),
      (∀ (x : X) (g : Γ), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : Γ → X) g = X.ρ g x) ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = ∑ᶠ c : Γ ⧸ U, X.ρ c.out ((f : Γ → X) (c.out)⁻¹)) ∧
      Function.Surjective τ.hom ∧
      Function.Injective i.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = 0 ↔ ∃ κ : K, i.hom κ = f) ∧
      (∀ (f : Rep.coind U.subtype (Rep.res U.subtype X)) (g : Γ),
        ((i.hom (E.hom f) : Rep.coind U.subtype (Rep.res U.subtype X)) : Γ → X) g = X.ρ φ ((f : Γ → X) (φ⁻¹ * g)) - (f : Γ → X) g) ∧
      Function.Injective ι.hom ∧ Function.Surjective E.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), E.hom f = 0 ↔ ∃ x : X, ι.hom x = f) := by
  obtain ⟨ι, τ, hι, hτ, hτs, -⟩ := Rep.exists_hom_coind_res_comp_eq_index_smul U X
  obtain ⟨K, i, E, h1, h2, h3, h4, h5, h6⟩ := Rep.exists_ker_trace_cyclicShift U φ hφ X ι τ hι hτ
  exact ⟨ι, τ, K, i, E, hι, hτ, hτs, h1, h2, h3, h4, h5, h6⟩

variable (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

theorem restrict_mem_levelCocycles₂ (U : Subgroup Γ) (M : Rep.{w} k Γ) {b : Γ × Γ → M}
    (hb : b ∈ levelCocycles₂ r M) :
    (fun g : U × U => b ((g.1 : Γ), (g.2 : Γ))) ∈ levelCocycles₂ (r.comp U.subtype) (Rep.res U.subtype M) :=
  cochainsPullPush₂_mem_levelCocycles₂ (rH := r) (rG := r.comp U.subtype) (A := M) (B := Rep.res U.subtype M)
    U.subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hb

theorem restrict_mem_levelCoboundaries₂ (U : Subgroup Γ) (M : Rep.{w} k Γ) {b : Γ × Γ → M}
    (hb : b ∈ levelCoboundaries₂ r M) :
    (fun g : U × U => b ((g.1 : Γ), (g.2 : Γ))) ∈ levelCoboundaries₂ (r.comp U.subtype) (Rep.res U.subtype M) :=
  cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r) (rG := r.comp U.subtype) (A := M) (B := Rep.res U.subtype M)
    U.subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hb

theorem push_mem_levelCocycles₂ {M M' : Rep.{w} k Γ} (f : M ⟶ M') {b : Γ × Γ → M}
    (hb : b ∈ levelCocycles₂ r M) : (f.hom ∘ b) ∈ levelCocycles₂ r M' :=
  cochainsPullPush₂_mem_levelCocycles₂ (rH := r) (rG := r) (A := M) (B := M')
    (MonoidHom.id Γ) (fun _ => rfl) f.hom.toLinearMap (fun g a => Rep.hom_comm_apply f g a) hb

theorem push_mem_levelCoboundaries₂ {M M' : Rep.{w} k Γ} (f : M ⟶ M') {b : Γ × Γ → M}
    (hb : b ∈ levelCoboundaries₂ r M) : (f.hom ∘ b) ∈ levelCoboundaries₂ r M' :=
  cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r) (rG := r) (A := M) (B := M')
    (MonoidHom.id Γ) (fun _ => rfl) f.hom.toLinearMap (fun g a => Rep.hom_comm_apply f g a) hb

theorem evalOne_mem_levelCocycles₂ (U : Subgroup Γ) (X : Rep.{w} k Γ) {c : Γ × Γ → Rep.coind U.subtype (Rep.res U.subtype X)}
    (hc : c ∈ levelCocycles₂ r (Rep.coind U.subtype (Rep.res U.subtype X))) :
    (fun g : U × U => ((c ((g.1 : Γ), (g.2 : Γ)) : Rep.coind U.subtype (Rep.res U.subtype X)) : Γ → X) 1)
      ∈ levelCocycles₂ (r.comp U.subtype) (Rep.res U.subtype X) := by
  let ev : Rep.coind U.subtype (Rep.res U.subtype X) →ₗ[k] X :=
    { toFun := fun f => (f : Γ → X) 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ (u : U) (f : Rep.coind U.subtype (Rep.res U.subtype X)),
      ev ((Rep.coind U.subtype (Rep.res U.subtype X)).ρ (U.subtype u) f) = (Rep.res U.subtype X).ρ u (ev f) := by
    intro u f
    show (f : Γ → X) (1 * (u : Γ)) = X.ρ (u : Γ) ((f : Γ → X) 1)
    have h := f.2 u 1
    rw [one_mul]
    rw [mul_one] at h
    exact h
  exact cochainsPullPush₂_mem_levelCocycles₂ (rH := r) (rG := r.comp U.subtype) (A := Rep.coind U.subtype (Rep.res U.subtype X))
    (B := Rep.res U.subtype X) U.subtype (fun _ => rfl) ev hev hc

theorem comp_hom_apply' {X Y Z : Rep.{w} k Γ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

theorem smul_hom_apply' {X Y : Rep.{w} k Γ} (c : k) (f : X ⟶ Y) (x : X) : (c • f).hom x = c • f.hom x := rfl

theorem smooth_of_injective {K Y : Rep.{w} k Γ} (i : K ⟶ Y) (hi : Function.Injective i.hom)
    (hY : ∀ y : Y, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : Γ, r s ∈ F.fixingSubgroup → Y.ρ s y = y) :
    ∀ κ : K, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : Γ, r s ∈ F.fixingSubgroup → K.ρ s κ = κ := by
  intro κ
  obtain ⟨F, hF, h⟩ := hY (i.hom κ)
  exact ⟨F, hF, fun s hs => hi (by rw [Rep.hom_comm_apply, h s hs])⟩

theorem comp_mem_cocycles₁ {C C' : Rep.{w} k Γ} (c : C ⟶ C') (x : cocycles₁ C) : (c.hom ∘ (x : Γ → C)) ∈ cocycles₁ C' := by
  rw [mem_cocycles₁_def]
  intro g h
  have := (mem_cocycles₁_def (x : Γ → C)).1 x.2 g h
  simp only [Function.comp_apply, ← Rep.hom_comm_apply, ← map_sub, ← map_add, this, map_zero]

theorem deltaCochain₁_zero_mem {A B C : Rep.{w} k Γ} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
    (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b) :
    deltaCochain₁ φ ψ hψ ((0 : cocycles₁ C) : Γ → C) ∈ levelCoboundaries₂ r A := by
  have hlc0 : IsLevelConstant₁ r ((0 : cocycles₁ C) : Γ → C) := ⟨⊥, inferInstance, fun _ _ _ => rfl⟩
  have hL : IsLevelConstant₁ r (0 : Γ → B) := ⟨⊥, inferInstance, fun _ _ _ => rfl⟩
  have h := groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2 r φ ψ hφ hψ hex 0 hlc0 0 hL
    (fun g => by show ψ.hom 0 = _; rw [map_zero]; rfl)
  have h0 : (preimageFun φ ∘ (d₁₂ B).hom (0 : Γ → B)) = 0 := by
    funext p
    show preimageFun φ (((d₁₂ B).hom 0) p) = 0
    rw [map_zero]
    show preimageFun φ 0 = 0
    rw [← map_zero φ.hom, preimageFun_apply φ hφ]
  rw [h0, zero_sub] at h
  exact (Submodule.neg_mem_iff _).1 h

theorem map_deltaCochain₁_sub_mem {A B C A' B' C' : Rep.{w} k Γ} (φ : A ⟶ B) (ψ : B ⟶ C) (φ' : A' ⟶ B') (ψ' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hsq1 : ∀ x : A, b.hom (φ.hom x) = φ'.hom (a.hom x)) (hsq2 : ∀ y : B, c.hom (ψ.hom y) = ψ'.hom (b.hom y))
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ y : B, ψ.hom y = 0 ↔ ∃ x : A, φ.hom x = y)
    (hφ' : Function.Injective φ'.hom) (hψ' : Function.Surjective ψ'.hom) (hex' : ∀ y : B', ψ'.hom y = 0 ↔ ∃ x : A', φ'.hom x = y)
    (x : cocycles₁ C) (hx : IsLevelConstant₁ r (x : Γ → C)) :
    (a.hom ∘ deltaCochain₁ φ ψ hψ (x : Γ → C)
      - deltaCochain₁ φ' ψ' hψ' ((⟨c.hom ∘ (x : Γ → C), comp_mem_cocycles₁ c x⟩ : cocycles₁ C') : Γ → C'))
      ∈ levelCoboundaries₂ r A' := by

  let L : Γ → B' := b.hom ∘ (Function.surjInv hψ ∘ (x : Γ → C))
  have hL : IsLevelConstant₁ r L := (hx.comp (Function.surjInv hψ)).comp b.hom
  have hLc : ∀ g, ψ'.hom (L g) = ((⟨c.hom ∘ (x : Γ → C), comp_mem_cocycles₁ c x⟩ : cocycles₁ C') : Γ → C') g := by
    intro g
    show ψ'.hom (b.hom (Function.surjInv hψ (x g))) = c.hom (x g)
    rw [← hsq2, Function.surjInv_eq hψ]
  have key := groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2 r φ' ψ' hφ' hψ' hex' _
    (hx.comp c.hom) L hL hLc

  have hd : (d₁₂ B').hom L = b.hom ∘ (d₁₂ B).hom (Function.surjInv hψ ∘ (x : Γ → C)) := by
    have := cochainsPullPush₂_d₁₂ (A := B) (B := B') (MonoidHom.id Γ) b.hom.toLinearMap
      (fun g y => Rep.hom_comm_apply b g y) (Function.surjInv hψ ∘ (x : Γ → C))

    exact this.symm
  have hrange : ∀ p : Γ × Γ, ∃ y : A, φ.hom y = (d₁₂ B).hom (Function.surjInv hψ ∘ (x : Γ → C)) p := by
    intro p
    apply (hex _).1
    have hψd := cochainsPullPush₂_d₁₂ (A := B) (B := C) (MonoidHom.id Γ) ψ.hom.toLinearMap
      (fun g y => Rep.hom_comm_apply ψ g y) (Function.surjInv hψ ∘ (x : Γ → C))
    have hσ : (cochainsPullPush₁ (MonoidHom.id Γ) ψ.hom.toLinearMap (Function.surjInv hψ ∘ (x : Γ → C))) = (x : Γ → C) := by
      funext g; show ψ.hom (Function.surjInv hψ (x g)) = x g; exact Function.surjInv_eq hψ _
    have : ψ.hom ((d₁₂ B).hom (Function.surjInv hψ ∘ (x : Γ → C)) p) =
        (cochainsPullPush₂ (MonoidHom.id Γ) ψ.hom.toLinearMap ((d₁₂ B).hom (Function.surjInv hψ ∘ (x : Γ → C)))) p := rfl
    rw [this, hψd, hσ]
    have hx0 : (d₁₂ C).hom (x : Γ → C) p = 0 := by
      obtain ⟨g, h⟩ := p
      rw [d₁₂_hom_apply, (mem_cocycles₁_iff (x : Γ → C)).1 x.2 g h]
      abel
    rw [hx0]
  have hident : (preimageFun φ' ∘ (d₁₂ B').hom L) = a.hom ∘ deltaCochain₁ φ ψ hψ (x : Γ → C) := by
    funext p
    obtain ⟨y, hy⟩ := hrange p
    show preimageFun φ' ((d₁₂ B').hom L p) = a.hom (preimageFun φ ((d₁₂ B).hom (Function.surjInv hψ ∘ (x : Γ → C)) p))
    rw [hd]
    show preimageFun φ' (b.hom ((d₁₂ B).hom (Function.surjInv hψ ∘ (x : Γ → C)) p)) = _
    rw [← hy, preimageFun_apply φ hφ, hsq1, preimageFun_apply φ' hφ']
  rw [hident] at key
  exact key

theorem isLevelConstant₁_d₀₁ {X : Rep.{w} k Γ}
    (hX : ∀ x : X, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : Γ, r s ∈ F.fixingSubgroup → X.ρ s x = x) (x : X) :
    IsLevelConstant₁ r ((d₀₁ X).hom x) := by
  obtain ⟨F, hF, h⟩ := hX x
  refine ⟨F, hF, fun g s hs => ?_⟩
  rw [d₀₁_hom_apply, d₀₁_hom_apply, map_mul, Module.End.mul_apply, h s hs]

end P2mS26HD2

namespace P2mS26HD2
open groupCohomology
section tower
universe w'
variable {k Γ : Type w'} [Field k] [Group Γ] (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

set_option maxHeartbeats 12800000 in

theorem exists_sub_mem_levelCoboundaries₂_of_tower
    {A B C : Rep.{w'} k Γ} (α : A ⟶ B) (ψ : B ⟶ C)
    (hα : Function.Injective α.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, α.hom a = b)
    (hsmB : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : Γ, r s ∈ F.fixingSubgroup → B.ρ s b = b)
    (U₁ U₂ U₃ : Subgroup Γ) [U₁.Normal] [U₁.FiniteIndex] [U₂.Normal] [U₂.FiniteIndex] [U₃.Normal] [U₃.FiniteIndex]
    (h21 : U₂ ≤ U₁) (h32 : U₃ ≤ U₂)
    (hUo₁ : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U₁)
    (hUo₂ : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U₂)
    (hUo₃ : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ U₃)
    (φ : Γ) (hφ₃ : ∀ g : Γ, ∃ (n : ℤ) (u : Γ), u ∈ U₃ ∧ g = φ ^ n * u)
    (hm : (((U₃.relIndex U₂ : ℕ) : k)) = 0)
    (c₂ : levelCocycles₂ r C)
    (hkill₁ : (fun g : U₁ × U₁ => (c₂ : Γ × Γ → C) ((g.1 : Γ), (g.2 : Γ)))
      ∈ levelCoboundaries₂ (r.comp U₁.subtype) (Rep.res U₁.subtype C))
    (hkill₂ : ∀ b : U₁ × U₁ → A, b ∈ levelCocycles₂ (r.comp U₁.subtype) (Rep.res U₁.subtype A) →
      (fun g : U₂ × U₂ => b (Subgroup.inclusion h21 g.1, Subgroup.inclusion h21 g.2))
        ∈ levelCoboundaries₂ (r.comp U₂.subtype) (Rep.res U₂.subtype A)) :
    ∃ c ∈ levelCocycles₂ r B, (ψ.hom ∘ c - (c₂ : Γ × Γ → C)) ∈ levelCoboundaries₂ r C := by
  classical
  have hφ₂ : ∀ g : Γ, ∃ (n : ℤ) (u : Γ), u ∈ U₂ ∧ g = φ ^ n * u := fun g => by
    obtain ⟨n, u, hu, h⟩ := hφ₃ g; exact ⟨n, u, h32 hu, h⟩
  have hφ₁ : ∀ g : Γ, ∃ (n : ℤ) (u : Γ), u ∈ U₁ ∧ g = φ ^ n * u := fun g => by
    obtain ⟨n, u, hu, h⟩ := hφ₂ g; exact ⟨n, u, h21 hu, h⟩

  obtain ⟨ιA1, τA1, KA1, iA1, EA1, hιA1, hτA1, hτA1s, hiA1, hτiA1, hEA1, hιA1i, hEA1s, hkEA1⟩ := pkg U₁ φ hφ₁ A
  obtain ⟨ιB1, τB1, KB1, iB1, EB1, hιB1, hτB1, hτB1s, hiB1, hτiB1, hEB1, hιB1i, hEB1s, hkEB1⟩ := pkg U₁ φ hφ₁ B
  obtain ⟨ιC1, τC1, KC1, iC1, EC1, hιC1, hτC1, hτC1s, hiC1, hτiC1, hEC1, hιC1i, hEC1s, hkEC1⟩ := pkg U₁ φ hφ₁ C
  obtain ⟨ιA2, τA2, KA2, iA2, EA2, hιA2, hτA2, hτA2s, hiA2, hτiA2, hEA2, hιA2i, hEA2s, hkEA2⟩ := pkg U₂ φ hφ₂ A
  obtain ⟨ιA3, τA3, KA3, iA3, EA3, hιA3, hτA3, hτA3s, hiA3, hτiA3, hEA3, hιA3i, hEA3s, hkEA3⟩ := pkg U₃ φ hφ₃ A
  obtain ⟨ιB3, τB3, KB3, iB3, EB3, hιB3, hτB3, hτB3s, hiB3, hτiB3, hEB3, hιB3i, hEB3s, hkEB3⟩ := pkg U₃ φ hφ₃ B
  obtain ⟨ιC3, τC3, KC3, iC3, EC3, hιC3, hτC3, hτC3s, hiC3, hτiC3, hEC3, hιC3i, hEC3s, hkEC3⟩ := pkg U₃ φ hφ₃ C

  obtain ⟨Yα1, Kα1, hYα1, hKα1, hια1, hEα1, hτα1⟩ := Rep.exists_coind_map_ker_trace U₁ φ α ιA1 τA1 ιB1 τB1 hιA1 hτA1 hιB1 hτB1
    iA1 EA1 iB1 EB1 hiB1 hτiB1 hEA1 hEB1 hτiA1
  obtain ⟨Yψ1, Kψ1, hYψ1, hKψ1, hιψ1, hEψ1, hτψ1⟩ := Rep.exists_coind_map_ker_trace U₁ φ ψ ιB1 τB1 ιC1 τC1 hιB1 hτB1 hιC1 hτC1
    iB1 EB1 iC1 EC1 hiC1 hτiC1 hEB1 hEC1 hτiB1
  obtain ⟨⟨hYα1i, hYψ1s, hYex1⟩, ⟨hKα1i, hKψ1s, hKex1⟩⟩ := Rep.shortExact_coind_ker_trace U₁ α ψ hα hψ hex
    τA1 τB1 τC1 hτA1 hτB1 hτC1 iA1 iB1 iC1 hiA1 hτiA1 hiB1 hτiB1 hiC1 hτiC1 Yα1 Yψ1 hYα1 hYψ1 Kα1 Kψ1 hKα1 hKψ1
  obtain ⟨Yα3, Kα3, hYα3, hKα3, hια3, hEα3, hτα3⟩ := Rep.exists_coind_map_ker_trace U₃ φ α ιA3 τA3 ιB3 τB3 hιA3 hτA3 hιB3 hτB3
    iA3 EA3 iB3 EB3 hiB3 hτiB3 hEA3 hEB3 hτiA3
  obtain ⟨Yψ3, Kψ3, hYψ3, hKψ3, hιψ3, hEψ3, hτψ3⟩ := Rep.exists_coind_map_ker_trace U₃ φ ψ ιB3 τB3 ιC3 τC3 hιB3 hτB3 hιC3 hτC3
    iB3 EB3 iC3 EC3 hiC3 hτiC3 hEB3 hEC3 hτiB3
  obtain ⟨⟨hYα3i, hYψ3s, hYex3⟩, ⟨hKα3i, hKψ3s, hKex3⟩⟩ := Rep.shortExact_coind_ker_trace U₃ α ψ hα hψ hex
    τA3 τB3 τC3 hτA3 hτB3 hτC3 iA3 iB3 iC3 hiA3 hτiA3 hiB3 hτiB3 hiC3 hτiC3 Yα3 Yψ3 hYα3 hYψ3 Kα3 Kψ3 hKα3 hKψ3

  obtain ⟨jA12, jKA12, hjA12, hjKA12, hjιA12, hjEA12, hjτA12⟩ := Rep.exists_coind_inclusion_ker_trace U₁ U₂ h21 φ A
    ιA1 τA1 ιA2 τA2 hιA1 hτA1 hιA2 hτA2 iA1 EA1 iA2 EA2 hτiA1 hiA2 hτiA2 hEA1 hEA2
  obtain ⟨jA23, jKA23, hjA23, hjKA23, hjιA23, hjEA23, hjτA23⟩ := Rep.exists_coind_inclusion_ker_trace U₂ U₃ h32 φ A
    ιA2 τA2 ιA3 τA3 hιA2 hτA2 hιA3 hτA3 iA2 EA2 iA3 EA3 hτiA2 hiA3 hτiA3 hEA2 hEA3
  obtain ⟨jA13, jKA13, hjA13, hjKA13, hjιA13, hjEA13, hjτA13⟩ := Rep.exists_coind_inclusion_ker_trace U₁ U₃ (h32.trans h21) φ A
    ιA1 τA1 ιA3 τA3 hιA1 hτA1 hιA3 hτA3 iA1 EA1 iA3 EA3 hτiA1 hiA3 hτiA3 hEA1 hEA3
  obtain ⟨jB13, jKB13, hjB13, hjKB13, hjιB13, hjEB13, hjτB13⟩ := Rep.exists_coind_inclusion_ker_trace U₁ U₃ (h32.trans h21) φ B
    ιB1 τB1 ιB3 τB3 hιB1 hτB1 hιB3 hτB3 iB1 EB1 iB3 EB3 hτiB1 hiB3 hτiB3 hEB1 hEB3
  obtain ⟨jC13, jKC13, hjC13, hjKC13, hjιC13, hjEC13, hjτC13⟩ := Rep.exists_coind_inclusion_ker_trace U₁ U₃ (h32.trans h21) φ C
    ιC1 τC1 ιC3 τC3 hιC1 hτC1 hιC3 hτC3 iC1 EC1 iC3 EC3 hτiC1 hiC3 hτiC3 hEC1 hEC3

  have hsmRes : ∀ (U : Subgroup Γ), ∀ n : Rep.res U.subtype B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ s : U, r s ∈ F.fixingSubgroup → (Rep.res U.subtype B).ρ s n = n := by
    intro U n
    obtain ⟨F, hF, h⟩ := hsmB n
    exact ⟨F, hF, fun s hs => h (s : Γ) hs⟩
  have hsmYB1 := Rep.exists_level_coind_apply_eq_self r U₁ hUo₁ (Rep.res U₁.subtype B) (hsmRes U₁)
  have hsmYB3 := Rep.exists_level_coind_apply_eq_self r U₃ hUo₃ (Rep.res U₃.subtype B) (hsmRes U₃)
  have hsmKB1 := smooth_of_injective r iB1 hiB1 hsmYB1
  have hsmKB3 := smooth_of_injective r iB3 hiB3 hsmYB3

  have hdies₁ := hkill₁
  have hιc₂ : (ιC1.hom ∘ (c₂ : Γ × Γ → C)) ∈ levelCocycles₂ r (Rep.coind U₁.subtype (Rep.res U₁.subtype C)) :=
    push_mem_levelCocycles₂ r ιC1 c₂.2
  have hev₁ : (fun pq : ↥U₁ × ↥U₁ =>
      (((ιC1.hom ∘ (c₂ : Γ × Γ → C)) ((pq.1 : Γ), (pq.2 : Γ)) : Rep.coind U₁.subtype (Rep.res U₁.subtype C)) : Γ → C) 1)
      ∈ levelCoboundaries₂ (r.comp U₁.subtype) (Rep.res U₁.subtype C) := by
    have heq : (fun pq : ↥U₁ × ↥U₁ =>
        (((ιC1.hom ∘ (c₂ : Γ × Γ → C)) ((pq.1 : Γ), (pq.2 : Γ)) : Rep.coind U₁.subtype (Rep.res U₁.subtype C)) : Γ → C) 1)
        = fun g : ↥U₁ × ↥U₁ => (c₂ : Γ × Γ → C) ((g.1 : Γ), (g.2 : Γ)) := by
      funext pq
      show ((ιC1.hom ((c₂ : Γ × Γ → C) ((pq.1 : Γ), (pq.2 : Γ))) : Rep.coind U₁.subtype (Rep.res U₁.subtype C)) : Γ → C) 1 = _
      rw [hιC1, map_one]; rfl
    rw [heq]; exact hdies₁
  have hιc₂B : (ιC1.hom ∘ (c₂ : Γ × Γ → C)) ∈ levelCoboundaries₂ r (Rep.coind U₁.subtype (Rep.res U₁.subtype C)) :=
    groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 r U₁ hUo₁
      (Rep.res U₁.subtype C) _ hιc₂ hev₁
  obtain ⟨k₂, hk₂lc, hk₂⟩ := (groupCohomology.comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1 r
    ιC1 EC1 hιC1i hEC1s hkEC1 (c₂ : Γ × Γ → C)).1 hιc₂B

  have ho : deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1) ∈ levelCocycles₂ r KA1 :=
    groupCohomology.deltaCochain1_mem_levelCocycles2 r Kα1 Kψ1 hKα1i hKψ1s hKex1 hsmKB1 k₂ hk₂lc

  have hio : (iA1.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1)) ∈ levelCocycles₂ r (Rep.coind U₁.subtype (Rep.res U₁.subtype A)) :=
    push_mem_levelCocycles₂ r iA1 ho
  have hv := evalOne_mem_levelCocycles₂ r U₁ A hio
  have hvdies := hkill₂ _ hv
  have hjo : (iA2.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) ∈ levelCocycles₂ r (Rep.coind U₂.subtype (Rep.res U₂.subtype A)) :=
    push_mem_levelCocycles₂ r iA2 (push_mem_levelCocycles₂ r jKA12 ho)
  have hev₂ : (fun pq : ↥U₂ × ↥U₂ =>
      (((iA2.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) ((pq.1 : Γ), (pq.2 : Γ)) : Rep.coind U₂.subtype (Rep.res U₂.subtype A)) : Γ → A) 1)
      ∈ levelCoboundaries₂ (r.comp U₂.subtype) (Rep.res U₂.subtype A) := by
    have heq : (fun pq : ↥U₂ × ↥U₂ =>
        (((iA2.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) ((pq.1 : Γ), (pq.2 : Γ)) : Rep.coind U₂.subtype (Rep.res U₂.subtype A)) : Γ → A) 1)
        = fun g : ↥U₂ × ↥U₂ =>
          (((iA1.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1)) ((Subgroup.inclusion h21 g.1 : Γ), (Subgroup.inclusion h21 g.2 : Γ))
            : Rep.coind U₁.subtype (Rep.res U₁.subtype A)) : Γ → A) 1 := by
      funext pq
      show ((iA2.hom (jKA12.hom _) : Rep.coind U₂.subtype (Rep.res U₂.subtype A)) : Γ → A) 1 = ((iA1.hom _ : Rep.coind U₁.subtype (Rep.res U₁.subtype A)) : Γ → A) 1
      rw [← comp_hom_apply' jKA12 iA2, hjKA12, comp_hom_apply', hjA12]
      rfl
    rw [heq]; exact hvdies
  have hjoB : (iA2.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) ∈ levelCoboundaries₂ r (Rep.coind U₂.subtype (Rep.res U₂.subtype A)) :=
    groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 r U₂ hUo₂
      (Rep.res U₂.subtype A) _ hjo hev₂
  obtain ⟨a₁, ha₁lc, ha₁⟩ := (groupCohomology.comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1 r
    iA2 τA2 hiA2 hτA2s hτiA2 (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))).1 hjoB

  have hsq1A : ∀ κ : KA2, jA23.hom (iA2.hom κ) = iA3.hom (jKA23.hom κ) := fun κ => by
    rw [← comp_hom_apply', ← hjKA23, comp_hom_apply']
  have hsq2A : ∀ y : Rep.coind U₂.subtype (Rep.res U₂.subtype A), ((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A).hom (τA2.hom y) = τA3.hom (jA23.hom y) := by
    intro y
    rw [← comp_hom_apply' jA23 τA3, hjτA23, smul_hom_apply', smul_hom_apply']
    rfl
  have h5 := map_deltaCochain₁_sub_mem r iA2 τA2 iA3 τA3 jKA23 jA23 ((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A)
    hsq1A hsq2A hiA2 hτA2s hτiA2 hiA3 hτA3s hτiA3 a₁ ha₁lc
  have h5' : deltaCochain₁ iA3 τA3 hτA3s
      ((⟨((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A).hom ∘ (a₁ : Γ → A),
        comp_mem_cocycles₁ ((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A) a₁⟩ : cocycles₁ A) : Γ → A)
      ∈ levelCoboundaries₂ r KA3 := by
    have : ((⟨((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A).hom ∘ (a₁ : Γ → A),
        comp_mem_cocycles₁ ((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A) a₁⟩ : cocycles₁ A) : Γ → A)
        = ((0 : cocycles₁ A) : Γ → A) := by
      funext g
      show ((((U₃.relIndex U₂ : ℕ) : k)) • 𝟙 A).hom (a₁ g) = 0
      rw [smul_hom_apply', hm, zero_smul]
    rw [this]
    exact deltaCochain₁_zero_mem r iA3 τA3 hiA3 hτA3s hτiA3
  have hjδ : (jKA23.hom ∘ deltaCochain₁ iA2 τA2 hτA2s (a₁ : Γ → A)) ∈ levelCoboundaries₂ r KA3 := by
    have := Submodule.add_mem _ h5 h5'
    rwa [sub_add_cancel] at this
  have hjjo : (jKA23.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) ∈ levelCoboundaries₂ r KA3 := by
    have h := push_mem_levelCoboundaries₂ r jKA23 ha₁
    have heq : (jKA23.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1) - deltaCochain₁ iA2 τA2 hτA2s (a₁ : Γ → A)))
        = (jKA23.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) - (jKA23.hom ∘ deltaCochain₁ iA2 τA2 hτA2s (a₁ : Γ → A)) := by
      funext p; exact map_sub jKA23.hom _ _
    rw [heq] at h
    have := Submodule.add_mem _ h hjδ
    rwa [sub_add_cancel] at this

  have hjKAfun : ∀ κ : KA1, jKA23.hom (jKA12.hom κ) = jKA13.hom κ := fun κ => hiA3 (by
    apply Subtype.ext; funext g
    rw [← comp_hom_apply' jKA23 iA3, hjKA23, comp_hom_apply', hjA23, ← comp_hom_apply' jKA12 iA2, hjKA12,
      comp_hom_apply', hjA12, ← comp_hom_apply' jKA13 iA3, hjKA13, comp_hom_apply', hjA13])
  have sqα13 : ∀ x : KA1, jKB13.hom (Kα1.hom x) = Kα3.hom (jKA13.hom x) := fun x => hiB3 (by
    apply Subtype.ext; funext g
    rw [← comp_hom_apply' jKB13 iB3, hjKB13, comp_hom_apply', hjB13, ← comp_hom_apply' Kα1 iB1, hKα1, comp_hom_apply', hYα1,
      ← comp_hom_apply' Kα3 iB3, hKα3, comp_hom_apply', hYα3, ← comp_hom_apply' jKA13 iA3, hjKA13, comp_hom_apply', hjA13])
  have sqψ13 : ∀ x : KB1, jKC13.hom (Kψ1.hom x) = Kψ3.hom (jKB13.hom x) := fun x => hiC3 (by
    apply Subtype.ext; funext g
    rw [← comp_hom_apply' jKC13 iC3, hjKC13, comp_hom_apply', hjC13, ← comp_hom_apply' Kψ1 iC1, hKψ1, comp_hom_apply', hYψ1,
      ← comp_hom_apply' Kψ3 iC3, hKψ3, comp_hom_apply', hYψ3, ← comp_hom_apply' jKB13 iB3, hjKB13, comp_hom_apply', hjB13])
  have h6a := map_deltaCochain₁_sub_mem r Kα1 Kψ1 Kα3 Kψ3 jKA13 jKB13 jKC13 sqα13 sqψ13
    hKα1i hKψ1s hKex1 hKα3i hKψ3s hKex3 k₂ hk₂lc
  have hjjo' : (jKA13.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1)) ∈ levelCoboundaries₂ r KA3 := by
    have heq : (jKA13.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))
        = (jKA23.hom ∘ (jKA12.hom ∘ deltaCochain₁ Kα1 Kψ1 hKψ1s (k₂ : Γ → KC1))) := by
      funext p; exact (hjKAfun _).symm
    rw [heq]; exact hjjo
  have hδ3 : deltaCochain₁ Kα3 Kψ3 hKψ3s
      ((⟨jKC13.hom ∘ (k₂ : Γ → KC1), comp_mem_cocycles₁ jKC13 k₂⟩ : cocycles₁ KC3) : Γ → KC3)
      ∈ levelCoboundaries₂ r KA3 := by
    have := Submodule.sub_mem _ hjjo' h6a
    rwa [sub_sub_cancel] at this

  obtain ⟨κ, hκlc, hκ⟩ := (groupCohomology.deltaCochain1_mem_levelCoboundaries2_iff r Kα3 Kψ3 hKα3i hKψ3s hKex3 hsmKB3
    ⟨jKC13.hom ∘ (k₂ : Γ → KC1), comp_mem_cocycles₁ jKC13 k₂⟩ (hk₂lc.comp jKC13.hom)).1 hδ3
  obtain ⟨κ₀, hκ₀⟩ := hκ
  obtain ⟨β₀, hβ₀⟩ := hKψ3s κ₀
  let κ' : cocycles₁ KB3 := κ + ⟨(d₀₁ KB3).hom β₀, coboundaries₁_le_cocycles₁ KB3 ⟨β₀, rfl⟩⟩
  have hκ'lc : IsLevelConstant₁ r (κ' : Γ → KB3) :=
    (levelCochains₁ r KB3).add_mem hκlc (isLevelConstant₁_d₀₁ r hsmKB3 β₀)
  have hκ'eq : (Kψ3.hom ∘ (κ' : Γ → KB3)) = jKC13.hom ∘ (k₂ : Γ → KC1) := by
    funext g
    have h1 : (d₀₁ KC3).hom κ₀ g = jKC13.hom (k₂ g) - Kψ3.hom (κ g) := by
      have := congrArg (fun f : Γ → KC3 => f g) hκ₀; exact this
    show Kψ3.hom (κ g + (d₀₁ KB3).hom β₀ g) = jKC13.hom (k₂ g)
    rw [map_add, d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, hβ₀, ← d₀₁_hom_apply, h1]
    abel

  have hc : deltaCochain₁ ιB3 EB3 hEB3s (κ' : Γ → KB3) ∈ levelCocycles₂ r B :=
    groupCohomology.deltaCochain1_mem_levelCocycles2 r ιB3 EB3 hιB3i hEB3s hkEB3 hsmYB3 κ' hκ'lc
  have sqIψ1 : ∀ b : B, Yψ3.hom (ιB3.hom b) = ιC3.hom (ψ.hom b) := fun b => by
    rw [← comp_hom_apply', hιψ3, comp_hom_apply']
  have sqIψ2 : ∀ y : Rep.coind U₃.subtype (Rep.res U₃.subtype B), Kψ3.hom (EB3.hom y) = EC3.hom (Yψ3.hom y) := fun y => by
    rw [← comp_hom_apply', hEψ3, comp_hom_apply']
  have h6b := map_deltaCochain₁_sub_mem r ιB3 EB3 ιC3 EC3 ψ Yψ3 Kψ3 sqIψ1 sqIψ2
    hιB3i hEB3s hkEB3 hιC3i hEC3s hkEC3 κ' hκ'lc
  have sqI13a : ∀ c : C, jC13.hom (ιC1.hom c) = ιC3.hom ((𝟙 C : C ⟶ C).hom c) := fun c => by
    rw [← comp_hom_apply', hjιC13]; rfl
  have sqI13b : ∀ y : Rep.coind U₁.subtype (Rep.res U₁.subtype C), jKC13.hom (EC1.hom y) = EC3.hom (jC13.hom y) := fun y => by
    rw [← comp_hom_apply', hjEC13, comp_hom_apply']
  have h6c := map_deltaCochain₁_sub_mem r ιC1 EC1 ιC3 EC3 (𝟙 C) jC13 jKC13 sqI13a sqI13b
    hιC1i hEC1s hkEC1 hιC3i hEC3s hkEC3 k₂ hk₂lc

  have hfun : ((⟨Kψ3.hom ∘ (κ' : Γ → KB3), comp_mem_cocycles₁ Kψ3 κ'⟩ : cocycles₁ KC3) : Γ → KC3)
      = ((⟨jKC13.hom ∘ (k₂ : Γ → KC1), comp_mem_cocycles₁ jKC13 k₂⟩ : cocycles₁ KC3) : Γ → KC3) := hκ'eq
  have hid : ((𝟙 C : C ⟶ C).hom ∘ deltaCochain₁ ιC1 EC1 hEC1s (k₂ : Γ → KC1)) = deltaCochain₁ ιC1 EC1 hEC1s (k₂ : Γ → KC1) := rfl
  rw [hfun] at h6b
  rw [hid] at h6c
  have hfinal : (ψ.hom ∘ deltaCochain₁ ιB3 EB3 hEB3s (κ' : Γ → KB3) - (c₂ : Γ × Γ → C)) ∈ levelCoboundaries₂ r C := by
    have h1 := Submodule.sub_mem _ h6b h6c
    have h2 := Submodule.sub_mem _ h1 hk₂
    have heq : ψ.hom ∘ deltaCochain₁ ιB3 EB3 hEB3s (κ' : Γ → KB3) - (c₂ : Γ × Γ → C)
        = (ψ.hom ∘ deltaCochain₁ ιB3 EB3 hEB3s (κ' : Γ → KB3)
            - deltaCochain₁ ιC3 EC3 hEC3s ((⟨jKC13.hom ∘ (k₂ : Γ → KC1), comp_mem_cocycles₁ jKC13 k₂⟩ : cocycles₁ KC3) : Γ → KC3))
          - (deltaCochain₁ ιC1 EC1 hEC1s (k₂ : Γ → KC1)
            - deltaCochain₁ ιC3 EC3 hEC3s ((⟨jKC13.hom ∘ (k₂ : Γ → KC1), comp_mem_cocycles₁ jKC13 k₂⟩ : cocycles₁ KC3) : Γ → KC3))
          - ((c₂ : Γ × Γ → C) - deltaCochain₁ ιC1 EC1 hEC1s (k₂ : Γ → KC1)) := by abel
    rw [heq]; exact h2
  exact ⟨_, hc, hfinal⟩

end tower
end P2mS26HD2

namespace P2mS26HD2w
open CategoryTheory groupCohomology ExtCitation

noncomputable def T (q : Nat.Primes) [Fact (q : ℕ).Prime] (N : ℕ) : Subgroup (primeLocalGaloisGroup q) :=
  (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
      : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))

noncomputable def U (q : Nat.Primes) [Fact (q : ℕ).Prime] (S : Subgroup (primeLocalGaloisGroup q)) (N : ℕ) : Subgroup S :=
  Subgroup.comap S.subtype (T q N)

theorem uniform
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ (N : ℕ) (hle : (P2mS26HD2w.U q S N) ≤ (P2mS26HD2w.U q S N₀)), 0 < N ∧ N₀ ∣ N ∧
      ∀ (b : ↥(P2mS26HD2w.U q S N₀) × ↥(P2mS26HD2w.U q S N₀) → B),
        b ∈ levelCocycles₂ (((primeLocalToGlobal q).comp S.subtype).comp (P2mS26HD2w.U q S N₀).subtype) (Rep.res (P2mS26HD2w.U q S N₀).subtype B) →
        (fun g : ↥(P2mS26HD2w.U q S N) × ↥(P2mS26HD2w.U q S N) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
          ∈ levelCoboundaries₂ (((primeLocalToGlobal q).comp S.subtype).comp (P2mS26HD2w.U q S N).subtype) (Rep.res (P2mS26HD2w.U q S N).subtype B) := by
  exact groupCohomology.exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal q S hS B hsm N₀ hN₀

theorem levels
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (N : ℕ) (hN : 0 < N) :
    (P2mS26HD2w.U q S N).Normal ∧ (P2mS26HD2w.U q S N).FiniteIndex ∧
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      F.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ (P2mS26HD2w.U q S N)) ∧
    (∃ φ : S, ∀ g : S, ∃ (n : ℤ) (u : S), u ∈ (P2mS26HD2w.U q S N) ∧ g = φ ^ n * u) ∧
    (∀ N' : ℕ, N ∣ N' → (P2mS26HD2w.U q S N') ≤ (P2mS26HD2w.U q S N)) ∧
    (∃ N' : ℕ, 0 < N' ∧ N ∣ N' ∧ p ∣ ((P2mS26HD2w.U q S N')).relIndex (P2mS26HD2w.U q S N)) := by
  exact ExtCitation.comap_rootsOfUnity_levels_of_isOpen (p := p) q S hS N hN

theorem exists_kernel {p : ℕ} [Fact p.Prime] {S : Type} [Group S]
    (r : S →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {B C : Rep.{0} (ZMod p) S} (ψ : B ⟶ C) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hψ : Function.Surjective ψ.hom) :
    ∃ (A : Rep.{0} (ZMod p) S) (α : A ⟶ B), Function.Injective α.hom ∧
      (∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, α.hom a = b) ∧
      FiniteDimensional (ZMod p) A ∧ FiniteDimensional (ZMod p) C ∧
      (∀ a : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : S, r s ∈ F.fixingSubgroup → A.ρ s a = a) ∧
      (∀ c : C, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : S, r s ∈ F.fixingSubgroup → C.ρ s c = c) := by
  classical

  let W : Submodule (ZMod p) B :=
    { carrier := {b | ψ.hom b = 0}
      add_mem' := fun {a b} ha hb => by show ψ.hom (a + b) = 0; rw [map_add, ha, hb, add_zero]
      zero_mem' := by show ψ.hom 0 = 0; exact map_zero _
      smul_mem' := fun c {b} hb => by show ψ.hom (c • b) = 0; rw [map_smul, hb, smul_zero] }
  have memW : ∀ b : B, b ∈ W ↔ ψ.hom b = 0 := fun _ => Iff.rfl
  have hW : ∀ g : S, W ≤ W.comap (B.ρ g) := fun g b hb => by
    show ψ.hom (B.ρ g b) = 0
    rw [Rep.hom_comm_apply, (memW b).1 hb, map_zero]
  let A : Rep.{0} (ZMod p) S := Rep.subrepresentation B W hW
  let α : A ⟶ B := Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap A.ρ B.ρ W.subtype (fun g a => rfl))
  have hαapp : ∀ a : A, α.hom a = (a : B) := fun _ => rfl
  have hα : Function.Injective α.hom := fun a b hab => Subtype.ext (by simpa [hαapp] using hab)
  have hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, α.hom a = b := fun b =>
    ⟨fun hb => ⟨⟨b, (memW b).2 hb⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ (memW _).1 a.2⟩

  have hsmA : ∀ a : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → A.ρ s a = a := by
    intro a
    obtain ⟨F, hF, h⟩ := hsm (a : B)
    exact ⟨F, hF, fun s hs => Subtype.ext (h s hs)⟩
  have hsmC : ∀ c : C, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → C.ρ s c = c := by
    intro c
    obtain ⟨b, rfl⟩ := hψ c
    obtain ⟨F, hF, h⟩ := hsm b
    exact ⟨F, hF, fun s hs => by rw [← Rep.hom_comm_apply, h s hs]⟩
  haveI hfdA : FiniteDimensional (ZMod p) A := by
    show FiniteDimensional (ZMod p) W
    infer_instance
  haveI hfdC : FiniteDimensional (ZMod p) C := Module.Finite.of_surjective ψ.hom.toLinearMap hψ

  exact ⟨A, α, hα, hex, hfdA, hfdC, hsmA, hsmC⟩

end P2mS26HD2w

namespace P2mS26HD2w
open CategoryTheory groupCohomology

universe w'
variable {k Γ : Type w'} [CommRing k] [Group Γ] (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

theorem final_step {B C : Rep.{w'} k Γ} (ψ : B ⟶ C) (c₂ : levelCocycles₂ r C) (c : Γ × Γ → B)
    (hc : c ∈ levelCocycles₂ r B) (hfinal : (ψ.hom ∘ c - (c₂ : Γ × Γ → C)) ∈ levelCoboundaries₂ r C) :
    continuousH2MapHom r ψ (continuousH2π r B ⟨c, hc⟩) = continuousH2π r C c₂ := by
  show continuousH2π r C _ = continuousH2π r C c₂
  exact (Submodule.Quotient.eq _).2 hfinal

theorem restrict_restrict_mem {C : Rep.{w'} k Γ} (U₀ U₁ : Subgroup Γ) (hle : U₁ ≤ U₀) (c₂ : levelCocycles₂ r C)
    (hkill : ∀ b : ↥U₀ × ↥U₀ → C, b ∈ levelCocycles₂ (r.comp U₀.subtype) (Rep.res U₀.subtype C) →
      (fun g : ↥U₁ × ↥U₁ => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
        ∈ levelCoboundaries₂ (r.comp U₁.subtype) (Rep.res U₁.subtype C)) :
    (fun g : ↥U₁ × ↥U₁ => (c₂ : Γ × Γ → C) ((g.1 : Γ), (g.2 : Γ)))
      ∈ levelCoboundaries₂ (r.comp U₁.subtype) (Rep.res U₁.subtype C) :=
  hkill _ (P2mS26HD2.restrict_mem_levelCocycles₂ r U₀ C c₂.2)

end P2mS26HD2w

open P2mS26HD2 in
set_option maxHeartbeats 3200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    {B C : Rep (ZMod p) S} (ψ : B ⟶ C) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hψ : Function.Surjective ψ.hom) :
    Function.Surjective (continuousH2MapHom ((primeLocalToGlobal q).comp S.subtype) ψ) := by
  classical
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  obtain ⟨A, α, hα, hex, hfdA, hfdC, hsmA, hsmC⟩ :=
    P2mS26HD2w.exists_kernel (p := p) ((primeLocalToGlobal q).comp S.subtype) ψ hsm hψ
  haveI := hfdA
  haveI := hfdC
  intro x
  obtain ⟨c₂, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨N₁, hle₁, hN₁, -, hkill₁⟩ := P2mS26HD2w.uniform (p := p) q S hS C hsmC 1 one_pos
  obtain ⟨N₂, hle₂, hN₂, -, hkill₂⟩ := P2mS26HD2w.uniform (p := p) q S hS A hsmA N₁ hN₁
  obtain ⟨hUn₂, hUf₂, hUo₂, -, hanti₂, N₃, hN₃, hN₂₃, hpdvd⟩ := P2mS26HD2w.levels (p := p) q S hS N₂ hN₂
  have hle₃ : P2mS26HD2w.U q S N₃ ≤ P2mS26HD2w.U q S N₂ := hanti₂ N₃ hN₂₃
  obtain ⟨hUn₁, hUf₁, hUo₁, -, -, -⟩ := P2mS26HD2w.levels (p := p) q S hS N₁ hN₁
  obtain ⟨hUn₃, hUf₃, hUo₃, ⟨φ, hφ₃⟩, -, -⟩ := P2mS26HD2w.levels (p := p) q S hS N₃ hN₃
  haveI := hUn₁; haveI := hUf₁; haveI := hUn₂; haveI := hUf₂; haveI := hUn₃; haveI := hUf₃
  have hm0 : ((((P2mS26HD2w.U q S N₃).relIndex (P2mS26HD2w.U q S N₂) : ℕ) : ZMod p)) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).2 hpdvd
  have hdies₁ := P2mS26HD2w.restrict_restrict_mem (k := ZMod p) (Γ := ↥S) ((primeLocalToGlobal q).comp S.subtype)
    (P2mS26HD2w.U q S 1) (P2mS26HD2w.U q S N₁) hle₁ c₂ hkill₁
  obtain ⟨c, hc, hfinal⟩ := exists_sub_mem_levelCoboundaries₂_of_tower (k := ZMod p) (Γ := ↥S)
    ((primeLocalToGlobal q).comp S.subtype) (A := A) (B := B) (C := C) α ψ hα hψ hex hsm
    (P2mS26HD2w.U q S N₁) (P2mS26HD2w.U q S N₂) (P2mS26HD2w.U q S N₃) hle₂ hle₃ hUo₁ hUo₂ hUo₃ φ hφ₃ hm0 c₂ hdies₁ hkill₂
  exact ⟨continuousH2π ((primeLocalToGlobal q).comp S.subtype) B ⟨c, hc⟩,
    P2mS26HD2w.final_step (k := ZMod p) (Γ := ↥S) ((primeLocalToGlobal q).comp S.subtype) ψ c₂ c hc hfinal⟩

end S_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal (solution)
