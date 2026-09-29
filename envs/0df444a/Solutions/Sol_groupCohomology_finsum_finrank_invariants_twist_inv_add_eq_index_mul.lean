-- Prove2me | solution 1 for groupCohomology.finsum_finrank_invariants_twist_inv_add_eq_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1e3990c8-291b-57a0-a806-8e1941188a8b

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Theorems.Thm_ExtCitation_cycloChar_complexConjugation_eq_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

local instance CycBaseArchSplit.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance CycBaseArchSplit.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance CycBaseArchSplit.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance CycBaseArchSplit.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace CycBaseArchSplit

open Representation

lemma Complex.conj_eq_neg_of_sq_eq_neg_one {z : ℂ} (hz : z ^ 2 = -1) : starRingEnd ℂ z = -z := by
  have h : (z - Complex.I) * (z + Complex.I) = 0 := by
    have : (z - Complex.I) * (z + Complex.I) = z ^ 2 + 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, hz]; ring
  rcases mul_eq_zero.mp h with h1 | h1
  · rw [sub_eq_zero.mp h1, Complex.conj_I]
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, Complex.conj_I, neg_neg]

lemma complexConjugation_apply_of_sq_eq_neg_one {j : AlgebraicClosure ℚ} (hj : j ^ 2 = -1) :
    complexConjugation j = -j := by
  apply complexEmbedding.toRingHom.injective
  show complexEmbedding (complexConjugation j) = complexEmbedding (-j)
  rw [complexEmbedding_complexConjugation, map_neg]
  apply Complex.conj_eq_neg_of_sq_eq_neg_one
  rw [← map_pow, hj, map_neg, map_one]

lemma complexConjugation_ne_one : complexConjugation ≠ 1 := by
  obtain ⟨j, hj⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  intro h
  have h1 : complexConjugation j = j := by rw [h]; rfl
  rw [complexConjugation_apply_of_sq_eq_neg_one hj] at h1
  have hj0 : j = 0 := by
    have h2 : (2 : AlgebraicClosure ℚ) * j = 0 := by rw [two_mul]; nth_rewrite 1 [← h1]; exact neg_add_cancel j
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [hj0] at hj; norm_num at hj

lemma orderOf_complexConjugation : orderOf complexConjugation = 2 :=
  orderOf_eq_prime complexConjugation_sq complexConjugation_ne_one

lemma mem_zpowers_complexConjugation_iff {g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} :
    g ∈ Subgroup.zpowers complexConjugation ↔ g = 1 ∨ g = complexConjugation := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
        complexConjugation_sq, one_zpow]
    · right
      rw [zpow_add, zpow_one, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
        complexConjugation_sq, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

lemma mem_range_inl_iff (S : Finset Nat.Primes) {g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} :
    g ∈ (extArithLoc S (Sum.inl ())).range ↔ g = 1 ∨ g = complexConjugation := by
  rw [← mem_zpowers_complexConjugation_iff]
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [extArithLoc_inl]; exact (show ↥archimedeanDecomposition from a).2
  · intro hg
    exact MonoidHom.mem_range.mpr ⟨(⟨g, hg⟩ : ↥archimedeanDecomposition), rfl⟩

section orbits

variable (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

abbrev Ω := (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range

abbrev Pl := Quotient (MulAction.orbitRel ↥K.fixingSubgroup (Ω S))

abbrev T := Quotient (QuotientGroup.rightRel K.fixingSubgroup)

noncomputable def θ : T K → Pl S K :=
  Quotient.lift (s := QuotientGroup.rightRel K.fixingSubgroup)
    (fun x => Quotient.mk _ (x : Ω S))
    (fun x y hxy => Quotient.sound (by
      have hxy' := QuotientGroup.rightRel_apply.mp hxy
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ?_)
      refine ⟨⟨x * y⁻¹, by simpa using K.fixingSubgroup.inv_mem hxy'⟩, ?_⟩
      show ((x * y⁻¹ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • (y : Ω S)) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]))

lemma θ_mk (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    θ S K (Quotient.mk _ x) = Quotient.mk _ (x : Ω S) := rfl

lemma θ_surjective : Function.Surjective (θ S K) := fun q => by
  induction q using Quotient.inductionOn with
  | h y =>
    induction y using QuotientGroup.induction_on with
    | H x => exact ⟨Quotient.mk _ x, rfl⟩

scoped instance finite_T [K.fixingSubgroup.FiniteIndex] : Finite (T K) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel K.fixingSubgroup).symm

scoped instance finite_Pl [K.fixingSubgroup.FiniteIndex] : Finite (Pl S K) :=
  Finite.of_surjective _ (θ_surjective S K)

lemma card_T : Nat.card (T K) = K.fixingSubgroup.index :=
  Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel K.fixingSubgroup)

lemma θ_eq_iff (x x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    θ S K (Quotient.mk _ x) = θ S K (Quotient.mk _ x₀) ↔
      (Quotient.mk (QuotientGroup.rightRel K.fixingSubgroup) x = Quotient.mk _ x₀ ∨
        Quotient.mk (QuotientGroup.rightRel K.fixingSubgroup) x = Quotient.mk _ (x₀ * complexConjugation)) := by
  constructor
  · intro h
    rw [θ_mk, θ_mk] at h
    have h' := MulAction.orbitRel_apply.mp (Quotient.exact h)
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp h'
    change ((k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • (x₀ : Ω S)) = (x : Ω S) at hk
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mem_range_inl_iff] at hk
    rcases hk with hk | hk
    · left
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      have hx : (k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀ = x := inv_mul_eq_one.mp hk
      rw [← hx, show x₀ * ((k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀)⁻¹ =
        ((k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ by group]
      exact K.fixingSubgroup.inv_mem k.2
    · right
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      have hx : x = (k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀ * complexConjugation :=
        inv_mul_eq_iff_eq_mul.mp hk
      rw [hx, show x₀ * complexConjugation * ((k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀ *
        complexConjugation)⁻¹ = ((k : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ by group]
      exact K.fixingSubgroup.inv_mem k.2
  · rintro (h | h)
    · rw [h]
    · rw [h, θ_mk, θ_mk]
      apply Quotient.sound
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨1, ?_⟩)
      rw [one_smul]
      symm
      rw [QuotientGroup.eq, mem_range_inl_iff]
      right
      rw [show (x₀ * complexConjugation)⁻¹ * x₀ = complexConjugation⁻¹ by group, complexConjugation_inv]

lemma card_fiber (x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Nat.card {t : T K // θ S K t = θ S K (Quotient.mk _ x₀)} =
      if x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup then 1 else 2 := by
  have e : {t : T K // θ S K t = θ S K (Quotient.mk _ x₀)} ≃
      ↥({Quotient.mk (QuotientGroup.rightRel K.fixingSubgroup) x₀,
         Quotient.mk (QuotientGroup.rightRel K.fixingSubgroup) (x₀ * complexConjugation)} :
          Set (T K)) := by
    refine Equiv.subtypeEquivRight fun t => ?_
    induction t using Quotient.inductionOn with
    | h x =>
      rw [θ_eq_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Nat.card_congr e, Nat.card_coe_set_eq]
  have hiff : Quotient.mk (QuotientGroup.rightRel K.fixingSubgroup) x₀ =
      Quotient.mk _ (x₀ * complexConjugation) ↔ x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup := by
    rw [Quotient.eq (r := QuotientGroup.rightRel K.fixingSubgroup)]
    exact QuotientGroup.rightRel_apply
  by_cases hP : x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup
  · rw [if_pos hP, ← hiff.mpr hP, Set.pair_eq_singleton, Set.ncard_singleton]
  · rw [if_neg hP, Set.ncard_pair (fun h => hP (hiff.mp h))]

lemma finsum_card_fiber [K.fixingSubgroup.FiniteIndex] :
    ∑ᶠ v : Pl S K, Nat.card {t : T K // θ S K t = v} = K.fixingSubgroup.index := by
  haveI : Fintype (Pl S K) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, ← card_T K, ← Nat.card_congr (Equiv.sigmaFiberEquiv (θ S K)),
    Nat.card_sigma]

end orbits

end CycBaseArchSplit
p2m_reactivate "P2MW.S_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul.CycBaseArchSplit"

namespace CycBaseArchSplit

open Representation

variable {p : ℕ} [Fact p.Prime]

theorem finite_quotient_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ E] :
    Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ E.fixingSubgroup) :=
  Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen E)

theorem finiteIndex_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ E] : E.fixingSubgroup.FiniteIndex :=
  haveI := finite_quotient_fixingSubgroup E
  Subgroup.finiteIndex_of_finite_quotient

lemma mem_stabilizer_iff' (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : ↥K.fixingSubgroup) :
    h ∈ MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S) ↔
      ((h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 ∨
        (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = x₀ * complexConjugation * x₀⁻¹) := by
  rw [MulAction.mem_stabilizer_iff]
  change ((h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • (x₀ : Ω S)) = (x₀ : Ω S) ↔ _
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mem_range_inl_iff]
  constructor
  · rintro (h1 | h1)
    · left
      have h2 : (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀ = x₀ := inv_mul_eq_one.mp h1
      exact mul_right_cancel (h2.trans (one_mul x₀).symm)
    · right
      have h2 : x₀ = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀ * complexConjugation :=
        inv_mul_eq_iff_eq_mul.mp h1
      have h3 : x₀ * complexConjugation = (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀ := by
        rw [h2, mul_assoc ((h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * x₀),
          complexConjugation_mul_self, mul_one, ← h2]
      rw [h3, mul_inv_cancel_right]
  · rintro (h1 | h1)
    · left; rw [h1, one_mul, inv_mul_cancel]
    · right
      rw [h1, show (x₀ * complexConjugation * x₀⁻¹ * x₀)⁻¹ * x₀ = complexConjugation⁻¹ by group,
        complexConjugation_inv]

lemma invariants_res_eq_top {K : IntermediateField ℚ (AlgebraicClosure ℚ)} (D : Subgroup ↥K.fixingSubgroup)
    (hD : ∀ h ∈ D, h = 1) (X : Rep.{0} (ZMod p) ↥K.fixingSubgroup) :
    (Rep.res D.subtype X).ρ.invariants = ⊤ :=
  eq_top_iff.mpr fun v _ => (mem_invariants _ _).mpr fun h => by
    rw [show h = 1 from Subtype.ext (hD h.1 h.2), map_one]; rfl

lemma invariants_res_eq_ker {K : IntermediateField ℚ (AlgebraicClosure ℚ)} (D : Subgroup ↥K.fixingSubgroup)
    (d : ↥K.fixingSubgroup) (hd : d ∈ D) (hD : ∀ h ∈ D, h = 1 ∨ h = d)
    (X : Rep.{0} (ZMod p) ↥K.fixingSubgroup) :
    (Rep.res D.subtype X).ρ.invariants = LinearMap.ker (X.ρ d - 1) := by
  ext v
  simp only [mem_invariants, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h; exact h ⟨d, hd⟩
  · intro h g
    rcases hD g.1 g.2 with hg | hg
    · rw [show g = 1 from Subtype.ext hg, map_one]; rfl
    · rw [show g = ⟨d, hd⟩ from Subtype.ext hg]; exact h

lemma finrank_ker_add_one_add_finrank_ker_sub_one {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h2 : (2 : k) ≠ 0) (T : V →ₗ[k] V) (hT : T * T = 1) :
    Module.finrank k (LinearMap.ker (T + 1)) + Module.finrank k (LinearMap.ker (T - 1)) =
      Module.finrank k V := by
  have hTT : ∀ v, T (T v) = v := fun v => by rw [← Module.End.mul_apply, hT, Module.End.one_apply]
  have hinf : LinearMap.ker (T + 1) ⊓ LinearMap.ker (T - 1) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨h1, h2'⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
      Module.End.one_apply, sub_eq_zero] at h1 h2'
    rw [h2', ← two_smul k] at h1
    exact (Submodule.mem_bot k).mpr ((smul_eq_zero.mp h1).resolve_left h2)
  have hsup : LinearMap.ker (T + 1) ⊔ LinearMap.ker (T - 1) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    refine ⟨(2 : k)⁻¹ • (v - T v), ?_, (2 : k)⁻¹ • (v + T v), ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_smul, LinearMap.add_apply, Module.End.one_apply, map_sub, hTT,
        smul_eq_zero]
      right; abel
    · rw [LinearMap.mem_ker, map_smul, LinearMap.sub_apply, Module.End.one_apply, map_add, hTT,
        smul_eq_zero]
      right; abel
    · rw [← smul_add, sub_add_add_cancel, ← two_smul k, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (T + 1)) (LinearMap.ker (T - 1))
  rw [hinf, hsup, finrank_top, finrank_bot, add_zero] at h
  exact h.symm

omit [Fact p.Prime] in
lemma coe_mem_fixingSubgroup_of_sq_eq_one (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p) (hp : p = 2)
    (d : ↥K.fixingSubgroup) (hd : d ^ 2 = 1) :
    (d : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup := by
  haveI hN' : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal :=
    ⟨fun s hs g => by
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      simpa using hnorm g g.2 s hs⟩
  have hq2 : orderOf (QuotientGroup.mk (s := L.fixingSubgroup.subgroupOf K.fixingSubgroup) d) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hd, QuotientGroup.mk_one])
  have hqi : orderOf (QuotientGroup.mk (s := L.fixingSubgroup.subgroupOf K.fixingSubgroup) d) ∣
      L.fixingSubgroup.relIndex K.fixingSubgroup :=
    orderOf_dvd_natCard _
  have hcop2 : Nat.Coprime (L.fixingSubgroup.relIndex K.fixingSubgroup) 2 := hp ▸ hcop
  have h1 : orderOf (QuotientGroup.mk (s := L.fixingSubgroup.subgroupOf K.fixingSubgroup) d) ∣ 1 := by
    have h := Nat.dvd_gcd hqi hq2
    rwa [Nat.Coprime.gcd_eq_one hcop2] at h
  have hq1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)

omit [Fact p.Prime] in
lemma p_ne_two_of_conj_mem (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hP : x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup) : p ≠ 2 := by
  intro hp
  obtain ⟨i, hiL, hi⟩ := h4 hp
  have hd2 : (⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ : ↥K.fixingSubgroup) ^ 2 = 1 :=
    Subtype.ext (by
      show (x₀ * complexConjugation * x₀⁻¹) ^ 2 = 1
      rw [conj_pow, complexConjugation_sq, mul_one, mul_inv_cancel])
  have hL' := coe_mem_fixingSubgroup_of_sq_eq_one K L hnorm hcop hp _ hd2
  have hfix : (x₀ * complexConjugation * x₀⁻¹) i = i :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hL' i hiL
  have hj : (x₀⁻¹ i) ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, complexConjugation_apply_of_sq_eq_neg_one hj, map_neg,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hfix
  have hi0 : i = 0 := by
    have h2 : (2 : AlgebraicClosure ℚ) * i = 0 := by
      rw [two_mul]; nth_rewrite 1 [← hfix]; exact neg_add_cancel i
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [hi0] at hi; norm_num at hi

end CycBaseArchSplit
p2m_reactivate "P2MW.S_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul.CycBaseArchSplit"

namespace CycBaseArchSplit

open Representation

variable {p : ℕ} [Fact p.Prime]

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h0'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h0')

lemma twist_inv_rho_conj (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup)
    (x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hP : x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup) :
    (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹).ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ =
      -(N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩) := by
  have hχd : cycloChar p (x₀ * complexConjugation * x₀⁻¹) = -1 := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, ExtCitation.cycloChar_complexConjugation_eq_neg_one p]
  show N.ρ.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹ _ = _
  rw [Representation.twist_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hχd,
    inv_neg_one, Units.val_neg, Units.val_one, neg_smul, one_smul]

lemma term_real (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hP : x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup) :
    Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants +
      Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype N).ρ.invariants =
    Module.finrank (ZMod p) N := by
  have hp2 : p ≠ 2 := p_ne_two_of_conj_mem K L hnorm hcop h4 x₀ hP
  have hdD : (⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ : ↥K.fixingSubgroup) ∈
      MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S) :=
    (mem_stabilizer_iff' S K x₀ _).mpr (Or.inr rfl)
  have hD : ∀ h ∈ MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S),
      h = 1 ∨ h = ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ := fun h hh => by
    rcases (mem_stabilizer_iff' S K x₀ h).mp hh with h1 | h1
    · left; exact Subtype.ext h1
    · right; exact Subtype.ext h1
  have hρ2 := twist_inv_rho_conj K N x₀ hP
  have f1 : Module.finrank (ZMod p)
      (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype N).ρ.invariants =
      Module.finrank (ZMod p) (LinearMap.ker (N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ - 1)) := by
    rw [invariants_res_eq_ker _ _ hdD hD N]
  have f2 : Module.finrank (ZMod p)
      (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants =
      Module.finrank (ZMod p) (LinearMap.ker (N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ + 1)) := by
    rw [invariants_res_eq_ker _ _ hdD hD (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹), hρ2,
      show -(N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩) - 1 = -(N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ + 1)
        from (neg_add' _ _).symm, LinearMap.ker_neg]
  have hT : N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ * N.ρ ⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ = 1 := by
    rw [← map_mul, ← sq, show (⟨x₀ * complexConjugation * x₀⁻¹, hP⟩ : ↥K.fixingSubgroup) ^ 2 = 1 from
      Subtype.ext (by
        show (x₀ * complexConjugation * x₀⁻¹) ^ 2 = 1
        rw [conj_pow, complexConjugation_sq, mul_one, mul_inv_cancel]), map_one]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  rw [f1, f2]
  exact finrank_ker_add_one_add_finrank_ker_sub_one h2 _ hT

lemma term_complex (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hP : x₀ * complexConjugation * x₀⁻¹ ∉ K.fixingSubgroup) :
    Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants +
      Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype N).ρ.invariants =
    2 * Module.finrank (ZMod p) N := by
  have hD : ∀ h ∈ MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S), h = 1 := fun h hh => by
    rcases (mem_stabilizer_iff' S K x₀ h).mp hh with h1 | h1
    · exact Subtype.ext h1
    · exact absurd (h1 ▸ h.2) hP
  have f1 : Module.finrank (ZMod p)
      (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype N).ρ.invariants =
      Module.finrank (ZMod p) N := by
    rw [invariants_res_eq_top _ hD N, finrank_top]
  have f2 : Module.finrank (ZMod p)
      (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) (x₀ : Ω S)).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants =
      Module.finrank (ZMod p) N := by
    rw [invariants_res_eq_top _ hD _, finrank_top]
  rw [f1, f2]; ring

lemma term_eq (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N] (v : Pl S K) :
    Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants +
      Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants =
    Nat.card {t : T K // θ S K t = v} * Module.finrank (ZMod p) N := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (x₀ : Ω S) = v.out :=
    ⟨v.out.out, QuotientGroup.out_eq' _⟩
  have hv : θ S K (Quotient.mk _ x₀) = v := by rw [θ_mk, hx₀]; exact Quotient.out_eq v
  rw [← hx₀, ← hv, card_fiber]
  by_cases hP : x₀ * complexConjugation * x₀⁻¹ ∈ K.fixingSubgroup
  · rw [if_pos hP, one_mul]; exact term_real S K L hnorm hcop h4 N x₀ hP
  · rw [if_neg hP]; exact term_complex S K N x₀ hP

end CycBaseArchSplit
p2m_reactivate "P2MW.S_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul.CycBaseArchSplit"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    (hKL : K ≤ L)
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
        ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
      (Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype
          (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants +
        Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants) =
      K.fixingSubgroup.index * Module.finrank (ZMod p) N := by
  haveI : FiniteDimensional ℚ K := hK.1
  haveI : K.fixingSubgroup.FiniteIndex := CycBaseArchSplit.finiteIndex_fixingSubgroup K
  rw [finsum_congr (CycBaseArchSplit.term_eq S K L hnorm hcop h4 N), ← finsum_mul,
    CycBaseArchSplit.finsum_card_fiber]

end S_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul
end P2MW
export P2MW.S_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul (solution)
