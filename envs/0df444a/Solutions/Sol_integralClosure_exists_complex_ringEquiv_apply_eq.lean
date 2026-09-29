-- Prove2me | solution 1 for integralClosure.exists_complex_ringEquiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2f1f0f29-c754-56de-906c-afb87bc89938

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_integralClosure_exists_complex_ringEquiv_apply_eq

open scoped Pointwise

namespace ZbarHomsConj

noncomputable section

theorem exists_ringEquiv_comp_eq {R S : Type*} [CommRing R] [Ring S]
    (φ ψ : R →+* S) (hker : RingHom.ker ψ = RingHom.ker φ)
    (hrange : Set.range ψ = Set.range φ) :
    ∃ τ : R ⧸ RingHom.ker φ ≃+* R ⧸ RingHom.ker φ,
      ∀ b : R, RingHom.kerLift φ (τ (Ideal.Quotient.mk _ b)) = ψ b := by

  let φb : R ⧸ RingHom.ker φ →+* S := RingHom.kerLift φ
  let ψb : R ⧸ RingHom.ker φ →+* S := Ideal.Quotient.lift _ ψ (fun a ha => by
    rw [← hker] at ha; exact (RingHom.mem_ker).mp ha)
  have hφb_inj : Function.Injective φb := RingHom.kerLift_injective φ
  have hψb_inj : Function.Injective ψb := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.lift_mk] at hq
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker]
    exact (RingHom.mem_ker).mpr hq
  have hmem : ∀ q, ψb q ∈ φb.range := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.lift_mk]
    obtain ⟨c, hc⟩ : ψ b ∈ Set.range φ := hrange ▸ ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [RingHom.kerLift_mk]; exact hc⟩
  let e₁ : R ⧸ RingHom.ker φ ≃+* φb.range :=
    RingEquiv.ofBijective (ψb.codRestrict φb.range hmem)
      ⟨fun x y hxy => hψb_inj (congrArg Subtype.val hxy), by
        rintro ⟨_, q, rfl⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
        obtain ⟨c, hc⟩ : φ b ∈ Set.range ψ := hrange.symm ▸ ⟨b, rfl⟩
        refine ⟨Ideal.Quotient.mk _ c, Subtype.ext ?_⟩
        change ψb _ = φb _
        rw [Ideal.Quotient.lift_mk, RingHom.kerLift_mk]
        exact hc⟩
  let e₂ : R ⧸ RingHom.ker φ ≃+* φb.range :=
    RingEquiv.ofBijective φb.rangeRestrict
      ⟨fun x y hxy => hφb_inj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  refine ⟨e₁.trans e₂.symm, fun b => ?_⟩
  have h2 : ∀ z, RingHom.kerLift φ z = (e₂ z : S) := fun z => rfl
  rw [h2, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  change ψb _ = _
  rw [Ideal.Quotient.lift_mk]

theorem splits_map_int (B F : Type*) [CommRing B] [Field F] [IsAlgClosed F]
    [Algebra B F] [IsIntegralClosure B ℤ F] {p : Polynomial ℤ} (hp : p.Monic) :
    (p.map (algebraMap ℤ B)).Splits := by
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B ℤ F).isDomain (algebraMap B F)
  refine Polynomial.Splits.of_splits_map_of_injective
    (IsIntegralClosure.algebraMap_injective B ℤ F) ?_ ?_
  · exact IsAlgClosed.splits _
  · intro a ha
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
    have hne : p.map (algebraMap ℤ F) ≠ 0 := (hp.map _).ne_zero
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map] at ha
    have hint : IsIntegral ℤ a := ⟨p, hp, ha⟩
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp hint
    exact ⟨b, hb⟩

theorem range_eq_setOf_isIntegral {B : Type*} (F : Type*) [CommRing B] [Field F] [IsAlgClosed F]
    [Algebra B F] [IsIntegralClosure B ℤ F] {k : Type*} [Field k] (χ : B →+* k) :
    Set.range χ = {t | IsIntegral ℤ t} := by
  haveI : Algebra.IsIntegral ℤ B := IsIntegralClosure.isIntegral_algebra ℤ F
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B ℤ F).isDomain (algebraMap B F)
  ext t
  constructor
  · rintro ⟨b, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) b).map χ.toIntAlgHom
  · rintro ⟨p, hp, hpt⟩
    have hs := splits_map_int B F hp
    have hq := hs.eq_prod_roots_of_monic (hp.map _)
    have hcomp : χ.comp (algebraMap ℤ B) = algebraMap ℤ k := RingHom.ext_int _ _
    have h0 : Polynomial.eval t ((p.map (algebraMap ℤ B)).map χ) = 0 := by
      rw [Polynomial.map_map, hcomp, Polynomial.eval_map]; exact hpt
    rw [hq, Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.prod_eq_zero_iff] at h0
    simp only [Multiset.map_map, Function.comp, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Multiset.mem_map] at h0
    obtain ⟨b, -, hb⟩ := h0
    exact ⟨b, (sub_eq_zero.mp hb).symm⟩

theorem isAlgClosure_rat (F : Type*) [Field F] [CharZero F] [IsAlgClosed F]
    [Algebra.IsAlgebraic ℚ F] : IsAlgClosure ℚ F := ⟨‹_›, ‹_›⟩

theorem isFractionRing_aux (B F : Type*) [CommRing B] [IsDomain B] [Field F] [CharZero F]
    [Algebra B F] [Algebra.IsAlgebraic ℚ F] [IsIntegralClosure B ℤ F] : IsFractionRing B F :=
  haveI : Algebra.IsAlgebraic ℤ F := IsFractionRing.comap_isAlgebraic_iff (K := ℚ) |>.mpr ‹_›
  IsIntegralClosure.isFractionRing_of_algebraic ℤ B
    (fun x hx => by simpa using hx)

set_option synthInstance.maxHeartbeats 320000 in

theorem core {B F : Type*} [CommRing B] [IsDomain B] [Field F] [CharZero F] [IsAlgClosed F]
    [Algebra B F] [Algebra.IsAlgebraic ℚ F] [IsIntegralClosure B ℤ F]
    {k : Type*} [Field k] (φ ψ : B →+* k) :
    ∃ σ : F ≃+* F, ∀ x y : B, algebraMap B F y = σ (algebraMap B F x) → φ x = ψ y := by
  haveI : IsAlgClosure ℚ F := isAlgClosure_rat F
  haveI : IsGalois ℚ F := IsAlgClosure.isGalois ℚ F
  haveI : IsFractionRing B F := isFractionRing_aux B F
  letI : MulSemiringAction Gal(F/ℚ) B := IsIntegralClosure.MulSemiringAction ℤ ℚ F B
  haveI : Algebra.IsIntegral ℤ B := IsIntegralClosure.isIntegral_algebra ℤ F
  haveI : SMulDistribClass Gal(F/ℚ) B F := inferInstance
  haveI : IsGaloisGroup Gal(F/ℚ) ℤ B := IsGaloisGroup.of_isFractionRing Gal(F/ℚ) ℤ B ℚ F
  haveI : Algebra.IsInvariant ℤ B Gal(F/ℚ) := inferInstance
  haveI : SMulCommClass Gal(F/ℚ) ℤ B := inferInstance
  have hinj : Function.Injective (algebraMap B F) := IsIntegralClosure.algebraMap_injective B ℤ F
  have hact : ∀ (g : Gal(F/ℚ)) (b : B), algebraMap B F (g • b) = g (algebraMap B F b) :=
    fun g b => algebraMap_galRestrict_apply ℤ g b

  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  haveI : ContinuousSMul Gal(F/ℚ) B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro b
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {algebraMap B F b}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {algebraMap B F b}))
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    rw [MulAction.mem_stabilizer_iff]
    apply hinj
    rw [hact]
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ _)

  set P : Ideal B := RingHom.ker φ with hP
  set Q : Ideal B := RingHom.ker ψ with hQ
  haveI hPp : P.IsPrime := RingHom.ker_isPrime φ
  haveI hQp : Q.IsPrime := RingHom.ker_isPrime ψ
  have hunder : P.under ℤ = Q.under ℤ := by
    simp only [Ideal.under, hP, hQ, RingHom.comap_ker]
    rw [RingHom.ext_int (φ.comp (algebraMap ℤ B)) (ψ.comp (algebraMap ℤ B))]
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := Gal(F/ℚ)) P Q hunder

  let ψ' : B →+* k := ψ.comp (MulSemiringAction.toRingHom Gal(F/ℚ) B g)
  have hψ' : ∀ b, ψ' b = ψ (g • b) := fun b => rfl
  have hker : RingHom.ker ψ' = RingHom.ker φ := by
    ext b
    rw [RingHom.mem_ker, hψ', ← RingHom.mem_ker, ← hQ, ← hP, hg]
    exact Ideal.smul_mem_pointwise_smul_iff
  have hrange : Set.range ψ' = Set.range φ := by
    rw [range_eq_setOf_isIntegral F ψ', range_eq_setOf_isIntegral F φ]

  obtain ⟨τ, hτ⟩ := exists_ringEquiv_comp_eq φ ψ' hker hrange
  have hτcomm : ∀ a : ℤ ⧸ P.under ℤ,
      τ (algebraMap (ℤ ⧸ P.under ℤ) (B ⧸ P) a) = algebraMap (ℤ ⧸ P.under ℤ) (B ⧸ P) a := by
    intro a
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hn : (Ideal.Quotient.mk (P.under ℤ)) n = ((n : ℤ) : ℤ ⧸ P.under ℤ) := by
      rw [← map_intCast (Ideal.Quotient.mk (P.under ℤ)) n, Int.cast_id]
    rw [hn, map_intCast, map_intCast]
  let τa : (B ⧸ P) ≃ₐ[ℤ ⧸ P.under ℤ] (B ⧸ P) := AlgEquiv.ofRingEquiv (f := τ) hτcomm
  obtain ⟨h, hh⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Gal(F/ℚ)) (P.under ℤ) P τa
  have hhb : ∀ b : B, φ ((h : Gal(F/ℚ)) • b) = ψ (g • b) := by
    intro b
    have h1 : Ideal.Quotient.mk P ((h : Gal(F/ℚ)) • b) = τ (Ideal.Quotient.mk P b) := by
      have := congrArg (fun f => f (Ideal.Quotient.mk P b)) hh
      exact this
    calc φ ((h : Gal(F/ℚ)) • b)
        = RingHom.kerLift φ (Ideal.Quotient.mk _ ((h : Gal(F/ℚ)) • b)) :=
          (RingHom.kerLift_mk φ _).symm
      _ = RingHom.kerLift φ (τ (Ideal.Quotient.mk P b)) := congrArg (RingHom.kerLift φ) h1
      _ = ψ' b := hτ b
      _ = ψ (g • b) := hψ' b

  refine ⟨((g * (h : Gal(F/ℚ))⁻¹ : Gal(F/ℚ)) : F ≃ₐ[ℚ] F).toRingEquiv, fun x y hxy => ?_⟩
  have hy : y = (g * (h : Gal(F/ℚ))⁻¹) • x := by
    apply hinj
    rw [hact, hxy]
    rfl
  rw [hy, mul_smul, ← hhb, smul_inv_smul]

abbrev Qbar : Type := ↥(algebraicClosure ℚ ℂ)

abbrev Zbar : Type := ↥(integralClosure ℤ ℂ)

theorem mem_Qbar_of_mem_Zbar {x : ℂ} (hx : x ∈ integralClosure ℤ ℂ) :
    x ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  rw [mem_integralClosure_iff] at hx
  exact (hx.tower_top (A := ℚ)).isAlgebraic

def zbarToQbar : Zbar →+* Qbar where
  toFun b := ⟨(b : ℂ), mem_Qbar_of_mem_Zbar b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

scoped instance algebraZbarQbar : Algebra Zbar Qbar := zbarToQbar.toAlgebra

@[scoped simp] theorem algebraMap_Zbar_Qbar_apply (b : Zbar) :
    ((algebraMap Zbar Qbar b : Qbar) : ℂ) = (b : ℂ) := rfl

scoped instance : IsScalarTower Zbar Qbar ℂ :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem isIntegralClosure_Zbar_Qbar :
    @IsIntegralClosure Zbar ℤ Qbar _ _ _ (Ring.toIntAlgebra Qbar) _ where
  algebraMap_injective := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Qbar => (z : ℂ)) hxy
  isIntegral_iff := by
    intro x
    rw [← isIntegral_algHom_iff (algebraMap Qbar ℂ).toIntAlgHom (algebraMap Qbar ℂ).injective]
    constructor
    · intro hx
      refine ⟨⟨(x : ℂ), hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2

theorem isAlgClosed_Qbar : IsAlgClosed Qbar := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed

theorem isAlgebraic_Qbar : @Algebra.IsAlgebraic ℚ Qbar _ _ DivisionRing.toRatAlgebra := by
  convert algebraicClosure.isAlgebraic ℚ ℂ
  rfl
  rfl

theorem exists_ringEquiv_extend (σ : Qbar ≃+* Qbar) :
    ∃ Sg : ℂ ≃+* ℂ, ∀ x : Qbar, Sg (x : ℂ) = (σ x : ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Qbar ℂ
  haveI : IsAlgClosure (Algebra.adjoin Qbar (Set.range ((↑) : s → ℂ))) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  set R := Algebra.adjoin Qbar (Set.range ((↑) : s → ℂ)) with hR
  let e : R ≃+* R :=
    (hs.1.aevalEquiv.symm.toRingEquiv.trans (MvPolynomial.mapEquiv s σ)).trans
      hs.1.aevalEquiv.toRingEquiv
  have he : ∀ x : Qbar, e (algebraMap Qbar R x) = algebraMap Qbar R (σ x) := by
    intro x
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply,
      MvPolynomial.map_C]
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have h1 : (x : ℂ) = algebraMap R ℂ (algebraMap Qbar R x) := by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he, ← IsScalarTower.algebraMap_apply]
  rfl

theorem main (k : Type*) [Field k] (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y := by
  haveI : IsAlgClosed Qbar := isAlgClosed_Qbar
  haveI : @Algebra.IsAlgebraic ℚ Qbar _ _ DivisionRing.toRatAlgebra := isAlgebraic_Qbar
  haveI : @IsIntegralClosure Zbar ℤ Qbar _ _ _ (Ring.toIntAlgebra Qbar) _ :=
    isIntegralClosure_Zbar_Qbar
  obtain ⟨σ, hσ⟩ := core (B := Zbar) (F := Qbar) φ ψ
  obtain ⟨Sg, hSg⟩ := exists_ringEquiv_extend σ
  refine ⟨Sg, fun x y hxy => hσ x y ?_⟩
  apply Subtype.ext
  change (y : ℂ) = ((σ (algebraMap Zbar Qbar x) : Qbar) : ℂ)
  rw [hxy, ← hSg]
  rfl

end

end ZbarHomsConj
p2m_reactivate "P2MW.S_integralClosure_exists_complex_ringEquiv_apply_eq.ZbarHomsConj"

theorem solution (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y :=
  ZbarHomsConj.main k φ ψ

end S_integralClosure_exists_complex_ringEquiv_apply_eq
end P2MW
export P2MW.S_integralClosure_exists_complex_ringEquiv_apply_eq (solution)
