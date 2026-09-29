-- Prove2me | solution 1 for groupCohomology.bijective_theta1_of_trivial_line_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9e878355-f15e-5680-82eb-70964d32530a

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one
import Theorems.Thm_groupCohomology_exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
import Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
import Theorems.Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
import Theorems.Thm_groupCohomology_cup_mem_levelCocycles2
import Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_of_isOpen_of_primeLocal
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta1_of_trivial_line_of_isOpen
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

theorem solution {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (hχS : ∀ s : primeLocalGaloisGroup q, s ∈ S → (cycloChar p) (primeLocalToGlobal q s) = 1)
    (A : Rep (ZMod p) S) (hA : ∀ (s : S) (a : A), A.ρ s a = a) (hA1 : finrank (ZMod p) A = 1)
    (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
      (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] ZMod p)
    (hinvS : Function.Bijective invS)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) A →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₁) :
    Function.Bijective θ₁ := by
  classical
  haveI : Fact ((q : ℕ)).Prime := ⟨q.2⟩
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨K, hKfd, hKS⟩ := ExtCitation.exists_padicLevel_fixingSubgroup_eq_of_isOpen q S hS
  haveI := hKfd
  obtain ⟨ζ, hζ⟩ := ExtCitation.exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one (q : ℕ) p K
    (fun σ hσ => hχS σ (by rw [← hKS]; exact hσ))

  let G := PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)
  let e : ↥S ≃* (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) :=
    (MulEquiv.subgroupCongr hKS).symm.trans (IntermediateField.fixingSubgroupEquiv K)
  let rK : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal (q : ℕ)).comp (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)
  have hlevel := fun (E : IntermediateField K (PadicAlgCl (q : ℕ))) (hE : FiniteDimensional K E) => by
    haveI := hE
    exact IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le (q : ℕ) K E
  have hopen := fun (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F) => by
    haveI := hF
    exact IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm (q : ℕ) K F
  have hre' : ∀ τ, rK τ = ((primeLocalToGlobal q).comp S.subtype) (e.symm τ) :=
    fun _ => rfl
  have hre2 : ∀ t : ↥S, rK (e t) = ((primeLocalToGlobal q).comp S.subtype) t := by
    intro t
    rw [hre', MulEquiv.symm_apply_apply]

  have hχ1 : ∀ s : ↥S, cycloChar p (primeLocalToGlobal q s.1) = 1 := fun s => hχS s.1 s.2
  have hN : ∀ (s : ↥S) (x : ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp
      S.subtype)),
      (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp
        S.subtype)).ρ s x = x := by
    intro s x
    show ((cycloChar p (primeLocalToGlobal q s.1) : (ZMod p)ˣ) : ZMod p) • x = x
    rw [hχS s.1 s.2, Units.val_one, one_smul]
  have hD : ∀ (s : ↥S) (f : A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp
      S.subtype)),
      (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp
        S.subtype)).ρ s f = f := by
    intro s f
    apply LinearMap.ext
    intro a
    show ((cycloChar p (primeLocalToGlobal q s.1) : (ZMod p)ˣ) : ZMod p) • (f : Module.Dual (ZMod p) A) (A.ρ s⁻¹ a) = f a
    rw [hχS s.1 s.2, Units.val_one, one_smul, hA]

  haveI : Module.Finite (ZMod p) A := Module.finite_of_finrank_eq_succ hA1
  haveI hV₁ : FiniteDimensional (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp
      S.subtype) A) :=
    groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal q S hS A
      (fun a => ⟨⊥, inferInstance, fun s _ => hA s a⟩)
  let φAD : A ≃ₗ[ZMod p] (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp
      S.subtype)) :=
    LinearEquiv.ofFinrankEq A (Module.Dual (ZMod p) A) (by rw [Subspace.dual_finrank_eq])
  obtain ⟨-, ⟨eV⟩, -⟩ := groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv
    ((primeLocalToGlobal q).comp S.subtype)
    ((primeLocalToGlobal q).comp S.subtype)
    (MulEquiv.refl _) (fun _ => rfl) A
    (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))
    φAD (fun s a => (congrArg φAD (hA s a)).trans (hD s (φAD a)).symm)
  haveI hV₂ := LinearEquiv.finiteDimensional eV
  have hdim := eV.finrank_eq

  let b := Module.finBasisOfFinrankEq (ZMod p) A hA1
  let δ₀ : Module.Dual (ZMod p) A := b.coord 0
  have hδ₀ : ∀ a : A, δ₀ a • b 0 = a := by
    intro a
    have := b.sum_repr a
    rw [Fin.sum_univ_one] at this
    exact this
  have hδ₀inj : ∀ a : A, δ₀ a = 0 → a = 0 := by
    intro a ha
    rw [← hδ₀ a, ha, zero_smul]

  have hζΩ : IsPrimitiveRoot ((ζ : K) : PadicAlgCl (q : ℕ)) p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let ζu : (PadicAlgCl (q : ℕ))ˣ := (hζΩ.isUnit (NeZero.ne p)).unit
  have hζu : IsPrimitiveRoot ζu p := hζΩ.isUnit_unit (NeZero.ne p)
  have hζufix := fun σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ) =>
    groupCohomology.Kummer.smul_units_eq_self_of_mem_range (K := K) σ (α := ζu) ⟨ζ, (IsUnit.unit_spec _).symm⟩
  have hfix : ∀ (σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) (x : rootsOfUnity p (PadicAlgCl (q : ℕ))),
      (σ • x : rootsOfUnity p (PadicAlgCl (q : ℕ))) = x := by
    intro σ x
    apply Subtype.ext
    have hu : (x : (PadicAlgCl (q : ℕ))ˣ) ∈ Subgroup.zpowers ζu := by rw [hζu.zpowers_eq]; exact x.2
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hu
    show σ • (x : (PadicAlgCl (q : ℕ))ˣ) = x
    rw [← hi, smul_zpow', hζufix]
  have hκmul : ∀ {a' : (↥K)ˣ} {α' : (PadicAlgCl (q : ℕ))ˣ}
      (hα' : algebraMap K (PadicAlgCl (q : ℕ)) (a' : K) = (α' : PadicAlgCl (q : ℕ)) ^ p) (σ τ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)),
      Kummer.kummerCocycleRoots hα' (σ * τ) = Kummer.kummerCocycleRoots hα' σ * Kummer.kummerCocycleRoots hα' τ := by
    intro a' α' hα' σ τ
    have := Kummer.isMulCocycle₁_kummerCocycleRoots hα' σ τ
    rw [hfix] at this
    rw [this, mul_comm]
  have hκlevel : ∀ {a' : (↥K)ˣ} {α' : (PadicAlgCl (q : ℕ))ˣ}
      (hα' : algebraMap K (PadicAlgCl (q : ℕ)) (a' : K) = (α' : PadicAlgCl (q : ℕ)) ^ p),
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ), rK s ∈ F.fixingSubgroup → Kummer.kummerCocycleRoots hα' s = 1 := by
    intro a' α' hα'
    have hint : IsIntegral K ((α' : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ)) :=
      IsIntegral.of_pow hp.pos (by rw [← hα']; exact isIntegral_algebraMap)
    haveI : FiniteDimensional K (IntermediateField.adjoin K {((α' : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ))}) :=
      IntermediateField.adjoin.finiteDimensional hint
    obtain ⟨F, hF, hFE⟩ := hlevel (IntermediateField.adjoin K {((α' : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ))}) inferInstance
    refine ⟨F, hF, fun s hs => ?_⟩
    have hsα : s ((α' : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ)) = α' :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hFE s hs) _ (IntermediateField.mem_adjoin_simple_self K _)
    apply Subtype.ext
    show Kummer.kummerCocycle α' s = 1
    rw [Kummer.kummerCocycle_apply, div_eq_one]
    exact Units.ext hsα
  let Λ : Additive (rootsOfUnity p (PadicAlgCl (q : ℕ))) ≃+ ZMod p :=
    (hζu.zmodEquivZPowers.trans (MulEquiv.toAdditive (MulEquiv.subgroupCongr hζu.zpowers_eq))).symm

  have heval := Rep.isEquivariantBilinear_eval_dualTwist A
    (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
  have hsmD : ∀ f : A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype),
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup →
          (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s f = f :=
    fun f => ⟨⊥, inferInstance, fun s _ => hD s f⟩

  have hinj : Function.Injective θ₁ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, hf, hfx⟩ := (mem_continuousH1_iff _ _ _).1 x.2
    have hx0 : x = ⟨(H1π A).hom f, H1π_mem_continuousH1 _ A hf⟩ := Subtype.ext hfx.symm

    have hfadd : ∀ s t, f (s * t) = f s + f t := by
      intro s t
      rw [(mem_cocycles₁_iff (⇑f)).1 f.2 s t, hA, add_comm]
    by_contra hne
    have hf0 : ∃ s, f s ≠ 0 := by
      by_contra h
      apply hne
      rw [hx0]
      apply Subtype.ext
      show (H1π A).hom f = 0
      rw [H1π_eq_zero_iff]
      have : (⇑f) = 0 := funext fun s => by by_contra hs; exact h ⟨s, hs⟩
      rw [this]
      exact Submodule.zero_mem _
    obtain ⟨s₀, hs₀⟩ := hf0

    let χf : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) → ZMod p := fun σ => δ₀ (f (e.symm σ))
    have hχadd : ∀ σ τ, χf (σ * τ) = χf σ + χf τ := by
      intro σ τ
      show δ₀ (f (e.symm (σ * τ))) = δ₀ (f (e.symm σ)) + δ₀ (f (e.symm τ))
      rw [← map_add]
      congr 1
      rw [map_mul]
      exact hfadd _ _
    have hχlc : IsLevelConstant₁ rK χf := by
      obtain ⟨F, hF, h⟩ := hf
      refine ⟨F, hF, fun σ τ hτ => ?_⟩
      show δ₀ (f (e.symm (σ * τ))) = δ₀ (f (e.symm σ))
      congr 1
      rw [map_mul]
      have h2 := hτ
      rw [hre'] at h2
      exact h (e.symm σ) (e.symm τ) h2
    have hχ0 : ∃ σ, χf σ ≠ 0 := ⟨e s₀, fun h => hs₀ (hδ₀inj _ (by
      have : χf (e s₀) = δ₀ (f s₀) := by show δ₀ (f (e.symm (e s₀))) = _; rw [MulEquiv.symm_apply_apply]
      rw [← this]; exact h))⟩
    obtain ⟨a, α, hα, hnot⟩ := groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic (q : ℕ) K p rK
      hlevel hopen χf hχadd hχlc hχ0

    let ψ : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) → ZMod p := fun τ => Λ (Additive.ofMul (Kummer.kummerCocycleRoots hα τ))
    have hψadd : ∀ σ τ, ψ (σ * τ) = ψ σ + ψ τ := by
      intro σ τ
      show Λ _ = Λ _ + Λ _
      rw [← Λ.map_add, hκmul hα σ τ, ofMul_mul]
    let gf : ↥S → A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) :=
      fun t => ψ (e t) • δ₀
    have hgmem : gf ∈ cocycles₁ (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) :=
      (mem_cocycles₁_iff gf).2 fun s t => by
        show ψ (e (s * t)) • δ₀ = _ + ψ (e s) • δ₀
        rw [map_mul, hψadd, add_smul, add_comm]
        congr 1
        exact (hD s (gf t)).symm
    let g : cocycles₁ (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) := ⟨gf, hgmem⟩
    have hglc : IsLevelConstant₁ ((primeLocalToGlobal q).comp S.subtype) (⇑g) := by
      obtain ⟨F, hF, hF1⟩ := hκlevel hα
      refine ⟨F, hF, fun s t ht => ?_⟩
      show ψ (e (s * t)) • δ₀ = ψ (e s) • δ₀
      rw [map_mul, hψadd]
      have : Kummer.kummerCocycleRoots hα (e t) = 1 := hF1 (e t) (by rw [hre2]; exact ht)
      have hψt : ψ (e t) = 0 := by show Λ _ = 0; rw [this, ofMul_one, Λ.map_zero]
      rw [hψt, add_zero]
    let y : continuousH1 ((primeLocalToGlobal q).comp S.subtype)
        (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) :=
      ⟨(H1π _).hom g, H1π_mem_continuousH1 _ _ hglc⟩

    let e₂ : levelCocycles₂ ((primeLocalToGlobal q).comp S.subtype)
        (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) :=
      ⟨(cup _ heval f g : ↥S × ↥S → ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)),
        groupCohomology.cup_mem_levelCocycles2 _ _ heval hsmD f g hf hglc⟩
    have hval : θ₁ x y = invS (continuousH2π _ _ e₂) := by
      rw [hx0]
      exact hθ₁ f hf g hglc e₂ (fun st => congrFun (cup_coe _ heval f g) st)
    have hzero : (e₂ : ↥S × ↥S → ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp
        S.subtype))
        ∈ levelCoboundaries₂ ((primeLocalToGlobal q).comp S.subtype) _ := by
      rw [← continuousH2π_eq_zero_iff]
      have h0 : θ₁ x y = 0 := by rw [hx, LinearMap.zero_apply]
      rw [hval] at h0
      exact hinvS.1 (h0.trans (map_zero invS).symm)

    apply hnot
    obtain ⟨bS, hbSlc, hbS⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hzero
    let B : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) → Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p := fun σ => Λ.symm (bS (e.symm σ))
    have hBlc : IsLevelConstant₁ rK B := by
      obtain ⟨F, hF, h⟩ := hbSlc
      refine ⟨F, hF, fun σ τ hτ => ?_⟩
      show Λ.symm (bS (e.symm (σ * τ))) = Λ.symm (bS (e.symm σ))
      congr 1
      rw [map_mul]
      have h2 := hτ
      rw [hre'] at h2
      exact h (e.symm σ) (e.symm τ) h2
    refine (mem_levelCoboundaries₂_iff rK _ _).2 ⟨B, hBlc, ?_⟩
    have hρ : ∀ (σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) (m : Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p),
        (Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p).ρ σ m = m := by
      intro σ m
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, hfix]
      rfl
    funext στ
    obtain ⟨σ, τ⟩ := στ

    have he₂ : ∀ s t : ↥S, (e₂ : ↥S × ↥S → ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp
        S.subtype)) (s, t) = ψ (e t) * δ₀ (f s) := by
      intro s t
      show (cup _ heval f g) (s, t) = _
      rw [cup_apply]
      show (((A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s (g t) :
        Module.Dual (ZMod p) A) (f s)) = ψ (e t) * δ₀ (f s)
      rw [hD s (g t)]
      rfl
    have hbd : ∀ s t : ↥S, bS t - bS (s * t) + bS s = ψ (e t) * δ₀ (f s) := by
      intro s t
      have h1 : (d₁₂ _).hom bS (s, t) = _ := congrFun hbS (s, t)
      rw [d₁₂_hom_apply] at h1
      calc bS t - bS (s * t) + bS s
          = (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s (bS t)
              - bS (s * t) + bS s := by rw [hN s (bS t)]
        _ = _ := h1
        _ = ψ (e t) * δ₀ (f s) := he₂ s t
    show (d₁₂ _).hom B (σ, τ) = ((χf σ).val : ℤ) • (Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p).ρ σ (Additive.ofMul (Kummer.kummerCocycleRoots hα τ))
    rw [hρ σ (Additive.ofMul _), d₁₂_hom_apply, hρ σ (B τ)]
    show Λ.symm (bS (e.symm τ)) - Λ.symm (bS (e.symm (σ * τ))) + Λ.symm (bS (e.symm σ))
      = ((χf σ).val : ℤ) • Additive.ofMul (Kummer.kummerCocycleRoots hα τ)
    rw [map_mul, ← map_sub, ← map_add, hbd (e.symm σ) (e.symm τ), MulEquiv.apply_symm_apply, mul_comm]
    have hsm : δ₀ (f (e.symm σ)) * ψ τ = (χf σ).val • ψ τ := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [hsm, map_nsmul, AddEquiv.symm_apply_apply, natCast_zsmul]

  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Subspace.dual_finrank_eq]; exact hdim)).1 hinj

end S_groupCohomology_bijective_theta1_of_trivial_line_of_isOpen
end P2MW
export P2MW.S_groupCohomology_bijective_theta1_of_trivial_line_of_isOpen (solution)
