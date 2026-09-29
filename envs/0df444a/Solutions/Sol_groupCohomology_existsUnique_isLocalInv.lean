-- Prove2me | solution 1 for groupCohomology.existsUnique_isLocalInv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d2307cee-ab86-5e7f-8ae9-0a25971f495c

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_primeLocal
import Theorems.Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_existsUnique_isLocalInv
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory ExtCitation groupCohomology IntermediateField

private theorem pow_val_add_aux {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] (u : Ωˣ) (hu : u ^ p = 1) (a b : ZMod p) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) p, pow_add, pow_mul, hu, one_pow, mul_one]

private theorem pow_val_mul_aux {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] (u : Ωˣ) (hu : u ^ p = 1) (a b : ZMod p) :
    u ^ (a * b).val = (u ^ a.val) ^ b.val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ZMod.val_mul, ← pow_mul]
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) p, pow_add, pow_mul, hu, one_pow, mul_one]

private theorem pow_val_injective_aux {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] (u : Ωˣ) (hu : IsPrimitiveRoot u p)
    {a b : ZMod p} (h : u ^ a.val = u ^ b.val) : a = b := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.val_injective p (hu.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime] :
    ∃! f : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p, IsLocalInv p ζ q f := by
  classical
  have hq : (q : ℕ).Prime := Fact.out
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let Ω := PadicAlgCl (q : ℕ)
  let G := Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω
  let S : Set Ω := {x : Ω | x ^ ((q : ℕ) ^ p - 1) = 1}
  let L₀ : IntermediateField ℚ_[(q : ℕ)] Ω := IntermediateField.adjoin ℚ_[(q : ℕ)] S
  let r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := localGaloisToGlobal (q : ℕ)
  let Mμ : Rep (ZMod p) (primeLocalGaloisGroup q) := ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))
  let H := continuousH2 (primeLocalToGlobal q) Mμ
  haveI : IsGalois ℚ_[(q : ℕ)] Ω := IsAlgClosure.isGalois _ _

  obtain ⟨u, hu, φ, hs, hfin, hfrob, π, hπ, hN, z, hz, hcong, hne⟩ :=
    groupCohomology.exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness p ζ hζ q
  haveI : Normal ℚ_[(q : ℕ)] L₀ := hN
  let e : H := continuousH2π (primeLocalToGlobal q) Mμ ⟨z, hz⟩
  have he : e ≠ 0 := hne

  obtain ⟨hfinH, hrankH⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_primeLocal (p := p) q
  haveI : FiniteDimensional (ZMod p) H := hfinH

  have hinjT : Function.Injective (LinearMap.toSpanSingleton (ZMod p) H e) := by
    intro c d hcd
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply] at hcd
    have h1 : (c - d) • e = 0 := by rw [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact sub_eq_zero.1 h2
    · exact absurd h2 he
  have hsurjT : Function.Surjective (LinearMap.toSpanSingleton (ZMod p) H e) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_self]; exact hrankH.symm)).1 hinjT
  let Θ : ZMod p ≃ₗ[ZMod p] H := LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ZMod p) H e) ⟨hinjT, hsurjT⟩
  have hΘ : ∀ c : ZMod p, Θ c = c • e := fun c => by
    show LinearEquiv.ofBijective _ _ c = _
    rw [LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply]
  let f : H →ₗ[ZMod p] ZMod p := Θ.symm.toLinearMap
  have hfe : f e = 1 := by
    change Θ.symm e = 1
    conv_lhs => rw [show e = Θ 1 by rw [hΘ, one_smul]]
    exact Θ.symm_apply_apply 1
  have huniq : ∀ g : H →ₗ[ZMod p] ZMod p, g e = 1 → g = f := by
    intro g hg
    apply LinearMap.ext
    intro w
    obtain ⟨c, rfl⟩ := hsurjT w
    rw [LinearMap.toSpanSingleton_apply, map_smul, map_smul, hg, hfe]

  have hlevel : ∀ E : IntermediateField ℚ_[(q : ℕ)] Ω, FiniteDimensional ℚ_[(q : ℕ)] E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : G, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by
    intro E hE
    obtain ⟨F, hF, hle⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
      (fun U => U ≤ E.fixingSubgroup) (fun U V hVU hU => hVU.trans hU)).2 ⟨E, hE, le_rfl⟩
    exact ⟨F, hF, fun σ hσ => hle hσ⟩
  have hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField ℚ_[(q : ℕ)] Ω, FiniteDimensional ℚ_[(q : ℕ)] E ∧
        ∀ σ : G, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup := by
    intro F hF
    obtain ⟨E, hE, hle⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
      (fun U => U ≤ (F.fixingSubgroup).comap r) (fun U V hVU hU => hVU.trans hU)).1 ⟨F, hF, le_rfl⟩
    exact ⟨E, hE, fun σ hσ => hle hσ⟩

  have hιζ : IsPrimitiveRoot (padicEmbedding (q : ℕ) ζ) p :=
    hζ.map_of_injective (padicEmbedding (q : ℕ) : AlgebraicClosure ℚ →+* Ω).injective
  have huprim : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp (by rw [hu]; exact hιζ)
  have hup : u ^ p = 1 := huprim.pow_eq_one
  have hsmul : ∀ g : G, g (u : Ω) = (u : Ω) ^ ((cycloChar p (r g) : ZMod p)).val := by
    intro g
    rw [hu]
    change (show Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω from g) (padicEmbedding (q : ℕ) ζ) = _
    rw [← padicEmbedding_localGaloisToGlobal, ← map_pow]
    congr 1
    have hξu : IsUnit ζ := hζ.isUnit hp.ne_zero
    have hmem : hξu.unit ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
      rw [mem_rootsOfUnity]; ext
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hζ.pow_eq_one, Units.val_one]
    have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (localGaloisToGlobal (q : ℕ) g : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hmem
    first | simpa [IsUnit.unit_spec] using this | (have h_1 := this; simp [IsUnit.unit_spec] at h_1; exact h_1) | (have h_1 := this; simp [IsUnit.unit_spec] at h_1 ⊢; exact h_1) | exact (this)

  let uμ : rootsOfUnity p Ω := ⟨u, (mem_rootsOfUnity p u).2 hup⟩
  let μ : Rep ℤ G := Kummer.kummerRep ℚ_[(q : ℕ)] Ω p
  have hupow : ∀ n : ℕ, ((uμ ^ n : rootsOfUnity p Ω) : Ωˣ) = u ^ n := fun n => by
    rw [Subgroup.coe_pow]
  let T : ZMod p →+ μ :=
    { toFun := fun c => Additive.ofMul (uμ ^ c.val)
      map_zero' := by rw [ZMod.val_zero, pow_zero]; rfl
      map_add' := fun c d => by
        have h1 : uμ ^ (c + d).val = uμ ^ c.val * uμ ^ d.val := Subtype.ext (by
          rw [Subgroup.coe_mul, hupow, hupow, hupow]
          exact pow_val_add_aux u hup c d)
        show Additive.ofMul (uμ ^ (c + d).val) = Additive.ofMul (uμ ^ c.val) + Additive.ofMul (uμ ^ d.val)
        rw [h1]; rfl }
  have hT : ∀ c : ZMod p, T c = Additive.ofMul (uμ ^ c.val) := fun _ => rfl
  have hTval : ∀ c : ZMod p, ((Additive.toMul (T c) : rootsOfUnity p Ω) : Ωˣ) = u ^ c.val := fun c => by
    rw [hT, ← hupow]; rfl
  have hTinj : Function.Injective T := by
    intro c d h
    apply pow_val_injective_aux u huprim
    rw [← hTval, ← hTval, h]
  have hTsurj : ∀ m : μ, ∃ c : ZMod p, T c = m := by
    intro m
    have hm0 : ((Additive.toMul m : rootsOfUnity p Ω) : Ωˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 (Additive.toMul m).2
    have hm1 : (((Additive.toMul m : rootsOfUnity p Ω) : Ωˣ) : Ω) ^ p = 1 := by
      have h := congrArg (fun x : Ωˣ => (x : Ω)) hm0
      beta_reduce at h
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h
      exact h
    have huΩ : IsPrimitiveRoot (u : Ω) p := by rw [hu]; exact hιζ
    obtain ⟨i, hilt, hi⟩ := huΩ.eq_pow_of_pow_eq_one hm1
    refine ⟨(i : ZMod p), ?_⟩
    apply (Additive.toMul (α := rootsOfUnity p Ω)).injective
    apply Subtype.ext
    apply Units.ext
    rw [hTval, ZMod.val_natCast, Nat.mod_eq_of_lt hilt, Units.val_pow_eq_pow_val, hi]
  have hTρ : ∀ (g : G) (c : ZMod p), μ.ρ g (T c) = T (Mμ.ρ g c) := by
    intro g c
    apply (Additive.toMul (α := rootsOfUnity p Ω)).injective
    apply Subtype.ext
    apply Units.ext
    rw [hTval]
    change (show Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω from g) (((Additive.toMul (T c) : rootsOfUnity p Ω) : Ωˣ) : Ω)
      = ((u ^ ((((cycloChar p).comp (primeLocalToGlobal q)) g : ZMod p) * c).val : Ωˣ) : Ω)
    rw [hTval, pow_val_mul_aux u hup]
    simp only [Units.val_pow_eq_pow_val]
    rw [map_pow, hsmul g]
    rfl

  let incl : μ →ₗ[ℤ] Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω :=
    (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
  have hincl : ∀ m : μ, incl m = Additive.ofMul ((Additive.toMul m : rootsOfUnity p Ω) : Ωˣ) := fun _ => rfl
  have hψ : ∀ c : ZMod p, incl (T c) = Additive.ofMul (u ^ c.val) := fun c => by rw [hincl, hTval]

  obtain ⟨hjinj, -⟩ := groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
    (K := ℚ_[(q : ℕ)]) (Ω := Ω) p r hlevel hopen

  have hkey : ∀ w : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p,
      w ∈ levelCocycles₂ (primeLocalToGlobal q) Mμ →
      (fun g : G × G => (Additive.ofMul (u ^ (w g).val) : Additive Ωˣ)) ∈
        levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) →
      w ∈ levelCoboundaries₂ (primeLocalToGlobal q) Mμ := by
    intro w hw hcb

    have hTw_cocy : (fun g : G × G => T (w g)) ∈ cocycles₂ μ := by
      refine (mem_cocycles₂_iff (A := μ) _).2 (fun g h j => ?_)
      have e1 := (mem_cocycles₂_iff (A := Mμ) w).1 hw.1 g h j
      have e2 := congrArg T e1
      rw [map_add, map_add, ← hTρ] at e2
      exact e2
    have hTw_lc : IsLevelConstant₂ r (fun g : G × G => T (w g)) := by
      obtain ⟨F, hF, hF2⟩ := hw.2
      exact ⟨F, hF, fun g g' s s' hs1 hs2 => congrArg T (hF2 g g' s s' hs1 hs2)⟩
    have hTw : (fun g : G × G => T (w g)) ∈ levelCocycles₂ r μ := ⟨hTw_cocy, hTw_lc⟩

    have hj0 : continuousH2Map (rH := r) (rG := r) (A := μ) (B := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω)
        (MonoidHom.id _) (fun _ => rfl) incl (fun _ _ => rfl) (continuousH2π r μ ⟨_, hTw⟩) = 0 := by
      rw [continuousH2Map_continuousH2π, continuousH2π_eq_zero_iff, coe_levelCocycles₂Map]
      have e3 : (cochainsPullPush₂ (MonoidHom.id G) incl (fun g : G × G => T (w g))
          : G × G → Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω)
          = fun g : G × G => (Additive.ofMul (u ^ (w g).val) : Additive Ωˣ) := by
        funext g
        obtain ⟨g₁, g₂⟩ := g
        exact hψ (w (g₁, g₂))
      rw [e3]
      exact hcb
    have hTw0 : continuousH2π r μ ⟨_, hTw⟩ = 0 := hjinj (hj0.trans (map_zero _).symm)
    rw [continuousH2π_eq_zero_iff] at hTw0
    obtain ⟨b, hb_lc, hb⟩ := (mem_levelCoboundaries₂_iff r μ _).1 hTw0

    choose b' hb' using fun g => hTsurj (b g)
    refine (mem_levelCoboundaries₂_iff (primeLocalToGlobal q) Mμ w).2 ⟨b', ?_, ?_⟩
    · obtain ⟨F, hF, hF1⟩ := hb_lc
      refine ⟨F, hF, fun g s hs' => hTinj ?_⟩
      rw [hb', hb']
      exact hF1 g s hs'
    · funext g
      obtain ⟨g₁, g₂⟩ := g
      apply hTinj
      have e4 := congrFun hb (g₁, g₂)
      rw [d₁₂_hom_apply] at e4 ⊢
      rw [map_add, map_sub, ← hTρ, hb', hb', hb']
      exact e4

  refine ⟨f, ?_, fun g hg => huniq g (hg u hu φ hs hfin hfrob π hπ hN z hz hcong)⟩
  show IsLocalInv p ζ q f
  unfold IsLocalInv
  intro u' hu' φ' hs' hfin' hfrob' π' hπ' inst' z' hz' hcong'

  have hu'u : u' = u := Units.ext (hu'.trans hu.symm)
  subst u'
  have hπ'π : π' = π := Units.ext (Subtype.ext (hπ'.trans hπ.symm))
  subst π'
  have hφ'φ : φ' = φ := by
    apply AlgEquiv.ext
    intro x
    have h := IntermediateField.adjoin_algHom_ext ℚ_[(q : ℕ)] (s := S)
      (φ₁ := (φ' : L₀ →ₐ[ℚ_[(q : ℕ)]] L₀)) (φ₂ := (φ : L₀ →ₐ[ℚ_[(q : ℕ)]] L₀)) (fun x hx => by
        apply Subtype.ext
        change ((φ' ⟨x, IntermediateField.subset_adjoin _ _ hx⟩ : L₀) : Ω)
          = ((φ ⟨x, IntermediateField.subset_adjoin _ _ hx⟩ : L₀) : Ω)
        rw [hfrob' ⟨x, IntermediateField.subset_adjoin _ _ hx⟩ hx, hfrob ⟨x, IntermediateField.subset_adjoin _ _ hx⟩ hx])
    exact AlgHom.congr_fun h x
  subst φ'

  have hdiff : (fun g : G × G => (Additive.ofMul (u ^ ((z' - z) g).val) : Additive Ωˣ)) ∈
      levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) := by
    have e5 := Submodule.sub_mem _ hcong' hcong
    have e6 : (fun g : G × G => (Additive.ofMul (u ^ ((z' - z) g).val) : Additive Ωˣ))
        = ((fun g : G × G => Additive.ofMul (u ^ (z' g).val))
            - unitsInflate₂ L₀ (carryFun φ hs' hfin' (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) (Additive.ofMul π)))
          - ((fun g : G × G => Additive.ofMul (u ^ (z g).val))
            - unitsInflate₂ L₀ (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) (Additive.ofMul π))) := by
      funext g
      simp only [Pi.sub_apply, sub_sub_sub_cancel_right]
      have e7 : u ^ (z' g - z g).val = u ^ (z' g).val * (u ^ (z g).val)⁻¹ := by
        apply eq_mul_inv_of_mul_eq
        rw [← pow_val_add_aux u hup, sub_add_cancel]
      rw [e7, ofMul_mul, ofMul_inv, ← sub_eq_add_neg]
    rw [e6]
    exact e5
  have hw : z' - z ∈ levelCocycles₂ (primeLocalToGlobal q) Mμ := Submodule.sub_mem _ hz' hz
  have hwcb := hkey (z' - z) hw hdiff
  have hclass : continuousH2π (primeLocalToGlobal q) Mμ ⟨z', hz'⟩ = e := by
    rw [← sub_eq_zero]
    change continuousH2π (primeLocalToGlobal q) Mμ ⟨z', hz'⟩ - continuousH2π (primeLocalToGlobal q) Mμ ⟨z, hz⟩ = 0
    rw [← map_sub, continuousH2π_eq_zero_iff]
    exact hwcb
  rw [hclass]
  exact hfe

end S_groupCohomology_existsUnique_isLocalInv
end P2MW
export P2MW.S_groupCohomology_existsUnique_isLocalInv (solution)
