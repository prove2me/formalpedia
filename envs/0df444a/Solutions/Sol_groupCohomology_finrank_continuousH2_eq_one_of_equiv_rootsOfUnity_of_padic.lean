-- Prove2me | solution 1 for groupCohomology.finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d8df5091-5959-5d39-8254-f239b00df4a2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
import Theorems.Thm_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory

open groupCohomology IntermediateField

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (p : ℕ) [Fact p.Prime]
    (M : Rep (ZMod p) (PadicAlgCl q ≃ₐ[K] PadicAlgCl q))
    (e : M ≃+ Additive (rootsOfUnity p (PadicAlgCl q)))
    (he : ∀ (σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q) (m : M), Additive.toMul (e (M.ρ σ m)) = σ • Additive.toMul (e m)) :
    Module.Finite (ZMod p) (continuousH2 r M) ∧ Module.finrank (ZMod p) (continuousH2 r M) = 1 := by
  classical
  have hp : p.Prime := Fact.out
  let e' : M ≃+ (Kummer.kummerRep K (PadicAlgCl q) p) := e

  have he'ρ : ∀ (σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q) (m : M),
      e' (M.ρ σ m) = (Kummer.kummerRep K (PadicAlgCl q) p).ρ σ (e' m) := by
    intro σ m
    show e (M.ρ σ m) = _
    apply Additive.toMul.injective
    rw [he]
    rfl
  have he'ρ' : ∀ (σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q) (y : (Kummer.kummerRep K (PadicAlgCl q) p)),
      e'.symm ((Kummer.kummerRep K (PadicAlgCl q) p).ρ σ y) = M.ρ σ (e'.symm y) := by
    intro σ y
    apply e'.injective
    rw [he'ρ, e'.apply_symm_apply, e'.apply_symm_apply]

  have hF : ∀ f : levelCocycles₂ r M,
      ((e' : M → (Kummer.kummerRep K (PadicAlgCl q) p)) ∘ (f.1 : ((PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q)) → M)) ∈ levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p) := by
    intro f
    refine (mem_levelCocycles₂_iff r (Kummer.kummerRep K (PadicAlgCl q) p) _).2 ⟨(mem_cocycles₂_iff _).2 fun g h j => ?_, f.2.2.comp _⟩
    have h1 := (mem_cocycles₂_iff (f.1 : ((PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q)) → M)).1 f.2.1 g h j
    show e' (f.1 (g * h, j)) + e' (f.1 (g, h)) = (Kummer.kummerRep K (PadicAlgCl q) p).ρ g (e' (f.1 (h, j))) + e' (f.1 (g, h * j))
    rw [← he'ρ, ← map_add, ← map_add, h1]
  have hG : ∀ f : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p),
      ((e'.symm : (Kummer.kummerRep K (PadicAlgCl q) p) → M) ∘ (f.1 : ((PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q)) → (Kummer.kummerRep K (PadicAlgCl q) p))) ∈ levelCocycles₂ r M := by
    intro f
    refine (mem_levelCocycles₂_iff r M _).2 ⟨(mem_cocycles₂_iff _).2 fun g h j => ?_, f.2.2.comp _⟩
    have h1 := (mem_cocycles₂_iff (f.1 : ((PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q)) → (Kummer.kummerRep K (PadicAlgCl q) p))).1 f.2.1 g h j
    show e'.symm (f.1 (g * h, j)) + e'.symm (f.1 (g, h)) = M.ρ g (e'.symm (f.1 (h, j))) + e'.symm (f.1 (g, h * j))
    rw [← he'ρ', ← map_add, ← map_add, h1]
  let F₀ : levelCocycles₂ r M →ₗ[ℤ] levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p) :=
    ({ toFun := fun f => ⟨_, hF f⟩
       map_zero' := by
         apply Subtype.ext; funext x
         show e' ((0 : levelCocycles₂ r M).1 x) = (0 : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)).1 x
         exact map_zero e'
       map_add' := fun f g => by
         apply Subtype.ext; funext x
         show e' ((f + g).1 x) = e' (f.1 x) + e' (g.1 x)
         exact map_add e' (f.1 x) (g.1 x) } : levelCocycles₂ r M →+ levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)).toIntLinearMap
  let G₀ : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p) →ₗ[ℤ] levelCocycles₂ r M :=
    ({ toFun := fun f => ⟨_, hG f⟩
       map_zero' := by
         apply Subtype.ext; funext x
         show e'.symm ((0 : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)).1 x) = (0 : levelCocycles₂ r M).1 x
         exact map_zero e'.symm
       map_add' := fun f g => by
         apply Subtype.ext; funext x
         show e'.symm ((f + g).1 x) = e'.symm (f.1 x) + e'.symm (g.1 x)
         exact map_add e'.symm (f.1 x) (g.1 x) } : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p) →+ levelCocycles₂ r M).toIntLinearMap
  have hF₀ : ∀ (f : levelCocycles₂ r M) (x : ((PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q))), (F₀ f).1 x = e' (f.1 x) := fun _ _ => rfl
  have hG₀ : ∀ (f : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)) (x : ((PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q))), (G₀ f).1 x = e'.symm (f.1 x) := fun _ _ => rfl

  have hd : ∀ (x : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → M),
      (d₁₂ (Kummer.kummerRep K (PadicAlgCl q) p)).hom ((e' : M → (Kummer.kummerRep K (PadicAlgCl q) p)) ∘ x) = (e' : M → (Kummer.kummerRep K (PadicAlgCl q) p)) ∘ (d₁₂ M).hom x := by
    intro x
    funext gh
    obtain ⟨g, h⟩ := gh
    simp only [Function.comp_apply, d₁₂_hom_apply, map_add, map_sub, he'ρ]
  have hd' : ∀ (x : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → (Kummer.kummerRep K (PadicAlgCl q) p)),
      (d₁₂ M).hom ((e'.symm : (Kummer.kummerRep K (PadicAlgCl q) p) → M) ∘ x) = (e'.symm : (Kummer.kummerRep K (PadicAlgCl q) p) → M) ∘ (d₁₂ (Kummer.kummerRep K (PadicAlgCl q) p)).hom x := by
    intro x
    funext gh
    obtain ⟨g, h⟩ := gh
    simp only [Function.comp_apply, d₁₂_hom_apply, map_add, map_sub, he'ρ']

  let PM := (levelCoboundaries₂ r M).comap (levelCocycles₂ r M).subtype
  let PK := (levelCoboundaries₂ r (Kummer.kummerRep K (PadicAlgCl q) p)).comap (levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)).subtype
  have hPF : PM.restrictScalars ℤ ≤ PK.comap F₀ := by
    intro f hf
    change (F₀ f).1 ∈ levelCoboundaries₂ r (Kummer.kummerRep K (PadicAlgCl q) p)
    have hf' : f.1 ∈ levelCoboundaries₂ r M := hf
    rw [mem_levelCoboundaries₂_iff] at hf' ⊢
    obtain ⟨x, hx, hxf⟩ := hf'
    refine ⟨(e' : M → (Kummer.kummerRep K (PadicAlgCl q) p)) ∘ x, hx.comp _, ?_⟩
    rw [hd, hxf]
    rfl
  have hPG : PK ≤ (PM.restrictScalars ℤ).comap G₀ := by
    intro f hf
    change (G₀ f).1 ∈ levelCoboundaries₂ r M
    have hf' : f.1 ∈ levelCoboundaries₂ r (Kummer.kummerRep K (PadicAlgCl q) p) := hf
    rw [mem_levelCoboundaries₂_iff] at hf' ⊢
    obtain ⟨x, hx, hxf⟩ := hf'
    refine ⟨(e'.symm : (Kummer.kummerRep K (PadicAlgCl q) p) → M) ∘ x, hx.comp _, ?_⟩
    rw [hd', hxf]
    rfl
  let ε := Submodule.Quotient.restrictScalarsEquiv ℤ PM
  let Φ : continuousH2 r M →ₗ[ℤ] continuousH2 r (Kummer.kummerRep K (PadicAlgCl q) p) :=
    (Submodule.mapQ _ PK F₀ hPF).comp ε.symm.toLinearMap
  let Ψ : continuousH2 r (Kummer.kummerRep K (PadicAlgCl q) p) →ₗ[ℤ] continuousH2 r M :=
    ε.toLinearMap.comp (Submodule.mapQ PK _ G₀ hPG)
  have hΦ : ∀ f : levelCocycles₂ r M, Φ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (F₀ f) := by
    intro f
    change Submodule.mapQ _ PK F₀ hPF (ε.symm (Submodule.Quotient.mk f)) = _
    rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply]
    rfl
  have hΨ : ∀ f : levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p),
      Ψ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (G₀ f) := by
    intro f
    change ε (Submodule.mapQ PK _ G₀ hPG (Submodule.Quotient.mk f)) = _
    rw [Submodule.mapQ_apply, Submodule.Quotient.restrictScalarsEquiv_mk]
    rfl
  have hGF : ∀ f, G₀ (F₀ f) = f := fun f => Subtype.ext (funext fun x => by
    rw [hG₀, hF₀, e'.symm_apply_apply])
  have hFG : ∀ f, F₀ (G₀ f) = f := fun f => Subtype.ext (funext fun x => by
    rw [hF₀, hG₀, e'.apply_symm_apply])
  let Θ : continuousH2 r M ≃ₗ[ℤ] continuousH2 r (Kummer.kummerRep K (PadicAlgCl q) p) :=
    LinearEquiv.ofLinear Φ Ψ
      (LinearMap.ext fun x => by
        induction x using Submodule.Quotient.induction_on with | H f =>
        rw [LinearMap.comp_apply, hΨ, hΦ, hFG, LinearMap.id_apply])
      (LinearMap.ext fun x => by
        induction x using Submodule.Quotient.induction_on with | H f =>
        rw [LinearMap.comp_apply, hΦ, hΨ, hGF, LinearMap.id_apply])

  obtain ⟨hinj, hrange⟩ := groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
    (K := K) (Ω := PadicAlgCl q) p r hlevel hopen
  have hS3 := groupCohomology.natCard_torsionBy_continuousH2_units_eq_of_padic q K r hlevel hopen p
  have hrt := Submodule.ext fun x => (hrange x).trans (Submodule.mem_torsionBy_iff (p : ℤ) x).symm
  have h1 : Nat.card (continuousH2 r (Kummer.kummerRep K (PadicAlgCl q) p)) = Nat.card (LinearMap.range _) :=
    Nat.card_congr (LinearEquiv.ofInjective _ hinj).toEquiv
  have h2 := Nat.card_congr (LinearEquiv.ofEq _ _ hrt).toEquiv
  have hcardK : Nat.card (continuousH2 r (Kummer.kummerRep K (PadicAlgCl q) p)) = p := h1.trans (h2.trans hS3)
  have hcardM : Nat.card (continuousH2 r M) = p := by
    rw [Nat.card_congr Θ.toEquiv, hcardK]
  haveI : Finite (continuousH2 r M) := Nat.finite_of_card_ne_zero (by rw [hcardM]; exact hp.ne_zero)
  haveI : Module.Finite (ZMod p) (continuousH2 r M) := Module.Finite.of_finite
  refine ⟨inferInstance, ?_⟩
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod p) (V := continuousH2 r M)
  rw [hcardM, Nat.card_zmod] at hpow
  have : p ^ 1 = p ^ Module.finrank (ZMod p) (continuousH2 r M) := by rw [pow_one]; exact hpow
  exact (Nat.pow_right_injective hp.two_le this).symm

end S_groupCohomology_finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
end P2MW
export P2MW.S_groupCohomology_finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic (solution)
