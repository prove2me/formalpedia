-- Prove2me | solution 1 for groupCohomology.localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/3ba1f332-d352-565e-a031-1b5831f07ecd

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_localInv_apply_eq_valuation_of_carryFun
import Theorems.Thm_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory ExtCitation groupCohomology Polynomial

namespace P2M
namespace UnrSymb

section Layer

variable (q : ℕ) [Fact q.Prime]

set_option hygiene false in
local notation "Ω" => PadicAlgCl q

lemma setOf_pow_eq_one_eq_rootSet {K : Type*} [Field K] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    {x : Ω | x ^ n = 1} = ((X ^ n - C 1 : K[X])).rootSet Ω := by
  ext x
  rw [Polynomial.mem_rootSet, Set.mem_setOf_eq, and_iff_right (X_pow_sub_C_ne_zero hn 1)]
  simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]

lemma finite_setOf_pow_eq_one (n : ℕ) (hn : 0 < n) : ({x : Ω | x ^ n = 1} : Set Ω).Finite := by
  rw [setOf_pow_eq_one_eq_rootSet q (K := ℚ_[q]) n hn]
  exact Polynomial.rootSet_finite _ _

lemma finiteDimensional_adjoin_setOf_pow_eq_one (n : ℕ) (hn : 0 < n) :
    FiniteDimensional ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ n = 1}) := by
  haveI : Finite ({x : Ω | x ^ n = 1} : Set Ω) := (finite_setOf_pow_eq_one q n hn).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp only [eval₂_sub, eval₂_X_pow, map_one, eval₂_one, sub_eq_zero]
  exact hx

lemma normal_adjoin_setOf_pow_eq_one (n : ℕ) (hn : 0 < n) :
    Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ n = 1}) := by
  rw [setOf_pow_eq_one_eq_rootSet q (K := ℚ_[q]) n hn]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := ℚ_[q]) (L := Ω) (p := (X ^ n - C 1 : ℚ_[q][X]))
    (IsAlgClosed.splits _)
  exact Normal.of_isSplittingField (X ^ n - C 1 : ℚ_[q][X])

lemma mem_fixingSubgroup_adjoin_of_forall {S : Set Ω} (σ : Ω ≃ₐ[ℚ_[q]] Ω) (hσ : ∀ x ∈ S, σ x = x) :
    σ ∈ (IntermediateField.adjoin ℚ_[q] S).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : IntermediateField.adjoin ℚ_[q] S ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro g ⟨k, rfl⟩
    change (σ ^ k) y = y
    have h1 : σ y = y := hσ y hy
    have hsymm : σ.symm y = y := by
      conv_lhs => rw [← h1]
      exact σ.symm_apply_apply y
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, h1]; exact ih
    | pred k ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hsymm]; exact ih
  have hmem := hle hx
  rw [IntermediateField.mem_fixedField_iff] at hmem
  exact hmem σ (Subgroup.mem_zpowers σ)

lemma forall_of_mem_fixingSubgroup_adjoin {S : Set Ω} (σ : Ω ≃ₐ[ℚ_[q]] Ω)
    (hσ : σ ∈ (IntermediateField.adjoin ℚ_[q] S).fixingSubgroup) : ∀ x ∈ S, σ x = x := fun x hx =>
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x (IntermediateField.subset_adjoin ℚ_[q] S hx)

variable (L : IntermediateField ℚ_[q] Ω) [Normal ℚ_[q] L]

lemma restrictNormalHom_eq_one_iff (σ : Ω ≃ₐ[ℚ_[q]] Ω) :
    AlgEquiv.restrictNormalHom L σ = 1 ↔ σ ∈ L.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]

lemma coe_restrictNormalHom_apply (σ : Ω ≃ₐ[ℚ_[q]] Ω) (x : L) :
    ((AlgEquiv.restrictNormalHom L σ x : L) : Ω) = σ (x : Ω) :=
  AlgEquiv.restrictNormal_commutes σ L x

end Layer

section UExp

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

omit [Fact p.Prime] in
include hζ in
lemma pow_p_eq_one_of_eq_padicEmbedding (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) :
    u ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hu, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]

noncomputable def uExp (u : (PadicAlgCl q)ˣ) (y : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p) :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Additive (PadicAlgCl q)ˣ :=
  fun g => Additive.ofMul (u ^ (y g).val)

lemma uExp_intCast_smul (u : (PadicAlgCl q)ˣ) (hup : u ^ p = 1) (m : ℤ)
    (y : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p) :
    uExp p q u ((m : ZMod p) • y) = m • uExp p q u y := by
  funext g
  simp only [uExp, Pi.smul_apply, smul_eq_mul, ZMod.val_mul, ← ofMul_zpow]
  rw [← pow_eq_pow_mod _ hup, mul_comm, pow_mul, ← zpow_natCast]
  congr 1
  have hw : (u ^ (y g).val) ^ (p : ℤ) = 1 := by
    rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, hup, one_pow]
  rw [zpow_eq_zpow_emod ((m : ZMod p).val : ℤ) hw, zpow_eq_zpow_emod m hw, ZMod.val_intCast,
    Int.emod_emod_of_dvd _ (dvd_refl _)]

end UExp

section Char

variable {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ)
  (hχ : ∀ σ τ : G, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))

include hχ in
lemma cast_chi_mul (σ τ : G) : ((χ (σ * τ) : ℤ) : ZMod p) = ((χ σ : ℤ) : ZMod p) + ((χ τ : ℤ) : ZMod p) := by
  have e : ((χ σ + χ τ - χ (σ * τ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hχ σ τ)
  push_cast at e
  linear_combination -e

include hχ in
lemma cast_chi_one : ((χ 1 : ℤ) : ZMod p) = 0 := by
  have e := cast_chi_mul p χ hχ 1 1
  rw [mul_one] at e
  linear_combination -e

include hχ in
lemma cast_chi_inv (σ : G) : ((χ σ⁻¹ : ℤ) : ZMod p) = -((χ σ : ℤ) : ZMod p) := by
  have e := cast_chi_mul p χ hχ σ σ⁻¹
  rw [mul_inv_cancel, cast_chi_one p χ hχ] at e
  linear_combination -e

include hχ in
lemma cast_chi_pow (σ : G) (k : ℕ) : ((χ (σ ^ k) : ℤ) : ZMod p) = (k : ZMod p) * ((χ σ : ℤ) : ZMod p) := by
  induction k with
  | zero => rw [pow_zero, cast_chi_one p χ hχ, Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, cast_chi_mul p χ hχ, ih, Nat.cast_succ]; ring

omit [Group G] in
lemma dvd_chi_iff (σ : G) : (p : ℤ) ∣ χ σ ↔ ((χ σ : ℤ) : ZMod p) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).symm

end Char

end P2M.UnrSymb

open P2M.UnrSymb in
theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ)
    (χ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → ℤ) (hχlc : IsLevelConstant₁ (localGaloisToGlobal q) χ)
    (hχ : ∀ σ τ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q), (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (hKχ : ∀ σ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (∀ x : PadicAlgCl q, x ^ ((q : ℕ) ^ p - 1) = 1 → σ x = x) ↔ (p : ℤ) ∣ χ σ)
    (φ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) (hφ : ∀ x : PadicAlgCl q, x ^ ((q : ℕ) ^ p - 1) = 1 → φ x = x ^ (q : ℕ))
    (a : ℚ_[q]ˣ) (α : (PadicAlgCl q)ˣ) (hα : algebraMap ℚ_[q] (PadicAlgCl q) (a : ℚ_[q]) = (α : PadicAlgCl q) ^ p)
    (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
    (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (hcob : (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
        - (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) =>
            (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl q)).subtype).toIntLinearMap
              ((χ g.1) • (Kummer.kummerRep ℚ_[q] (PadicAlgCl q) p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2))))
        ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) :
    localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩)
      = ((χ φ : ℤ) : ZMod p) * (((Padic.valuation (a : ℚ_[q]) : ℤ)) : ZMod p) := by
  classical

  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hqP : ((q : ℕ)).Prime := Fact.out
  set n : ℕ := (q : ℕ) ^ p - 1 with hn
  have hn0 : 0 < n := by
    have := Nat.one_lt_pow (Fact.out : p.Prime).pos.ne' hqP.one_lt
    omega
  set S : Set (PadicAlgCl q) := {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1} with hS
  set L : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.adjoin ℚ_[q] S with hL
  haveI instFD : FiniteDimensional ℚ_[q] L := finiteDimensional_adjoin_setOf_pow_eq_one (q : ℕ) _ hn0
  haveI instN : Normal ℚ_[q] L := normal_adjoin_setOf_pow_eq_one (q : ℕ) _ hn0
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
  have hup : u ^ p = 1 := pow_p_eq_one_of_eq_padicEmbedding p ζ hζ q u hu

  have hfixS : ∀ σ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      σ ∈ L.fixingSubgroup ↔ ∀ x : PadicAlgCl q, x ^ ((q : ℕ) ^ p - 1) = 1 → σ x = x := fun σ =>
    ⟨fun h x hx => forall_of_mem_fixingSubgroup_adjoin (q : ℕ) σ h x hx,
      fun h => mem_fixingSubgroup_adjoin_of_forall (q : ℕ) σ (fun x hx => h x hx)⟩

  set t : ZMod p := ((χ φ : ℤ) : ZMod p) with ht
  have ht0 : t ≠ 0 := by
    intro h0
    have hφfix : ∀ x : PadicAlgCl q, x ^ ((q : ℕ) ^ p - 1) = 1 → φ x = x :=
      (hKχ φ).mpr ((dvd_chi_iff p χ φ).mpr h0)

    haveI : NeZero n := ⟨hn0.ne'⟩
    obtain ⟨ξ, hξ⟩ : ∃ ξ : PadicAlgCl q, IsPrimitiveRoot ξ n := HasEnoughRootsOfUnity.prim
    have h1 : φ ξ = ξ ^ (q : ℕ) := hφ ξ hξ.pow_eq_one
    have h2 : φ ξ = ξ := hφfix ξ hξ.pow_eq_one
    have h3 : ξ ^ ((q : ℕ) - 1) = 1 := by
      have hq1 : 1 ≤ (q : ℕ) := hqP.one_lt.le
      have e : ξ ^ (q : ℕ) = ξ := h1.symm.trans h2
      have e' : ξ ^ ((q : ℕ) - 1) * ξ = 1 * ξ := by
        rw [← pow_succ, Nat.sub_add_cancel hq1, one_mul, e]
      exact mul_right_cancel₀ (hξ.ne_zero hn0.ne') e'
    have hdvd : n ∣ (q : ℕ) - 1 := (hξ.pow_eq_one_iff_dvd _).mp h3
    have hlt : (q : ℕ) - 1 < n := by
      rw [hn]
      have : (q : ℕ) < (q : ℕ) ^ p := by
        calc (q : ℕ) = (q : ℕ) ^ 1 := (pow_one _).symm
          _ < (q : ℕ) ^ p := Nat.pow_lt_pow_right hqP.one_lt hp1
      omega
    have hpos : 0 < (q : ℕ) - 1 := by have := hqP.one_lt; omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)

  set t' : ℤ := ((t⁻¹ : ZMod p).val : ℤ) with ht'
  have htt : (t' : ZMod p) * t = 1 := by
    rw [ht', ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id, inv_mul_cancel₀ ht0]
  set χ' : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → ℤ := fun σ => t' * χ σ with hχ'def
  have hχ'lc : IsLevelConstant₁ (localGaloisToGlobal q) χ' := hχlc.comp (t' * ·)
  have hχ' : ∀ σ τ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q), (p : ℤ) ∣ χ' σ + χ' τ - χ' (σ * τ) := by
    intro σ τ
    have := hχ σ τ
    simp only [hχ'def, ← mul_add, ← mul_sub]
    exact this.mul_left t'
  have hcastχ' : ∀ σ, ((χ' σ : ℤ) : ZMod p) = (t' : ZMod p) * ((χ σ : ℤ) : ZMod p) := fun σ => by
    simp only [hχ'def, Int.cast_mul]
  have hKχ' : ∀ σ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q), σ ∈ L.fixingSubgroup ↔ (p : ℤ) ∣ χ' σ := by
    intro σ
    rw [hfixS, hKχ σ, dvd_chi_iff p χ, dvd_chi_iff p χ', hcastχ']
    constructor
    · intro h; rw [h, mul_zero]
    · intro h
      have e : ((χ σ : ℤ) : ZMod p) = t * ((t' : ZMod p) * ((χ σ : ℤ) : ZMod p)) := by
        rw [← mul_assoc, mul_comm t, htt, one_mul]
      rw [e, h, mul_zero]

  set φL : L ≃ₐ[ℚ_[q]] L := AlgEquiv.restrictNormalHom L φ with hφLdef
  have hφL : ∀ x : L, (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φL x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ) := by
    intro x hx
    rw [hφLdef, coe_restrictNormalHom_apply]
    exact hφ x hx
  have hfinL : IsOfFinOrder φL := isOfFinOrder_of_finite φL

  have hdecomp : ∀ σ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      σ * (φ ^ (((χ' σ : ℤ) : ZMod p).val))⁻¹ ∈ L.fixingSubgroup := by
    intro σ
    rw [hKχ' _, dvd_chi_iff p χ', cast_chi_mul p χ' hχ', cast_chi_inv p χ' hχ', cast_chi_pow p χ' hχ',
      hcastχ' φ, ← ht, htt, mul_one, ZMod.natCast_zmod_val, add_neg_cancel]
  have hsL : ∀ g : L ≃ₐ[ℚ_[q]] L, g ∈ Subgroup.zpowers φL := by
    intro g
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl q) g
    refine ⟨(((χ' σ : ℤ) : ZMod p).val : ℤ), ?_⟩
    have h1 : AlgEquiv.restrictNormalHom L (σ * (φ ^ (((χ' σ : ℤ) : ZMod p).val))⁻¹) = 1 :=
      (restrictNormalHom_eq_one_iff (q : ℕ) L _).mpr (hdecomp σ)
    rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h1
    change φL ^ ((((χ' σ : ℤ) : ZMod p).val : ℕ) : ℤ) = AlgEquiv.restrictNormalHom L σ
    rw [zpow_natCast, h1]
  have hsχ' : ∀ σ : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (p : ℤ) ∣ χ' σ - (cyclicLog φL hsL hfinL (AlgEquiv.restrictNormalHom L σ) : ℤ) := by
    intro σ
    set k : ℕ := cyclicLog φL hsL hfinL (AlgEquiv.restrictNormalHom L σ) with hk
    have hσk : AlgEquiv.restrictNormalHom L σ = φL ^ k := by
      have h := (finEquivZPowers hfinL).apply_symm_apply ⟨_, hsL (AlgEquiv.restrictNormalHom L σ)⟩
      rw [finEquivZPowers_apply] at h
      exact (congrArg Subtype.val h).symm
    have hmem : σ * (φ ^ k)⁻¹ ∈ L.fixingSubgroup := by
      rw [← restrictNormalHom_eq_one_iff (q : ℕ) L, map_mul, map_inv, map_pow, ← hφLdef, hσk, mul_inv_cancel]
    have hd : ((χ' (σ * (φ ^ k)⁻¹) : ℤ) : ZMod p) = 0 := (dvd_chi_iff p χ' _).mp ((hKχ' _).mp hmem)
    rw [cast_chi_mul p χ' hχ', cast_chi_inv p χ' hχ', cast_chi_pow p χ' hχ', hcastχ' φ, ← ht, htt, mul_one] at hd
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast]
    linear_combination hd

  have hlevel : ∀ E : IntermediateField ℚ_[q] (PadicAlgCl q), FiniteDimensional ℚ_[q] E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by
    intro E hE
    obtain ⟨F, hF, hle⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
      (fun U => U ≤ E.fixingSubgroup) (fun U V hVU hU => hVU.trans hU)).mpr ⟨E, hE, le_rfl⟩
    exact ⟨F, hF, fun σ hσ => hle (Subgroup.mem_comap.mpr hσ)⟩
  have REL1 := smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 (K := ℚ_[q]) (Ω := PadicAlgCl q)
    p (localGaloisToGlobal q) hlevel χ' hχ'lc hχ' L hKχ' φL hsL hfinL hsχ' a α hα

  set LC := levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) with hLC
  set cup : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Additive (PadicAlgCl q)ˣ :=
    fun g => (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl q)).subtype).toIntLinearMap
      ((χ g.1) • (Kummer.kummerRep ℚ_[q] (PadicAlgCl q) p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
    with hcupdef
  set cup' : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Additive (PadicAlgCl q)ˣ :=
    fun g => (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl q)).subtype).toIntLinearMap
      ((χ' g.1) • (Kummer.kummerRep ℚ_[q] (PadicAlgCl q) p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
    with hcup'def
  set αL : (L)ˣ := Units.map (algebraMap ℚ_[q] L).toMonoidHom a with hαLdef
  set cα := unitsInflate₂ L (carryFun φL hsL hfinL (A := Rep.ofAlgebraAutOnUnits ℚ_[q] L) (Additive.ofMul αL)) with hcα
  have hREL1 : cup' - cα ∈ LC := REL1
  have hcob0 : uExp p q u z - cup ∈ LC := hcob
  have hcup' : cup' = t' • cup := by
    funext g
    simp only [hcup'def, hcupdef, hχ'def, Pi.smul_apply, mul_smul]
    exact map_zsmul _ t' _
  have hz' : ((t' : ZMod p)) • z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :=
    Submodule.smul_mem _ _ hz
  have hcob' : uExp p q u (((t' : ZMod p)) • z) - cα ∈ LC := by
    have e : uExp p q u (((t' : ZMod p)) • z) - cα = t' • (uExp p q u z - cup) + (cup' - cα) := by
      rw [uExp_intCast_smul p q u hup, hcup']
      module
    rw [e]
    exact add_mem (LC.smul_mem t' hcob0) hREL1

  have hαL : ((αL : L) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (a : ℚ_[q]) := rfl
  have key := localInv_apply_eq_valuation_of_carryFun p ζ hζ q (a : ℚ_[q]) a.ne_zero u hu φL hsL hfinL hφL αL hαL
    instN _ hz' hcob'

  have hcls : continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨_, hz'⟩
      = ((t' : ZMod p)) • continuousH2π (primeLocalToGlobal q)
          (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩ := by
    rw [← map_smul]
    rfl
  rw [hcls, map_smul, smul_eq_mul] at key
  calc localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩)
      = t * ((t' : ZMod p) * localInv p ζ q (continuousH2π (primeLocalToGlobal q)
          (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩)) := by
        rw [← mul_assoc, mul_comm t, htt, one_mul]
    _ = t * (((Padic.valuation (a : ℚ_[q]) : ℤ)) : ZMod p) := by rw [key]

end S_groupCohomology_localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation
end P2MW
export P2MW.S_groupCohomology_localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation (solution)
