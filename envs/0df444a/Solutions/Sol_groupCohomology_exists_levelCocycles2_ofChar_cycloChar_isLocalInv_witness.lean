-- Prove2me | solution 1 for groupCohomology.exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d80adaf6-d6fe-588e-8c99-5048468db4f0

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCocycles2
import Theorems.Thm_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Theorems.Thm_groupCohomology_levelCoboundaries2_le_levelCocycles2
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow
import Theorems.Thm_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Theorems.Thm_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic
import Theorems.Thm_orderOf_unitOfCoprime_pow_sub_one
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Theorems.Thm_IsPrimitiveRoot_existsUnique_eq_pow_val
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory ExtCitation groupCohomology IntermediateField Polynomial

private theorem fd_normal_adjoin_rootsOfUnity_aux (F E : Type) [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (m : ℕ) (hm : 0 < m) :
    FiniteDimensional F (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}) ∧
      Normal F (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}) := by
  classical
  set P : F[X] := X ^ m - 1 with hP
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact Polynomial.X_pow_sub_C_ne_zero hm 1
  have hset : {ζ : E | ζ ^ m = 1} = P.rootSet E := by
    ext ζ
    rw [Polynomial.mem_rootSet, hP]
    simp only [Set.mem_setOf_eq, map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact ⟨fun h => ⟨hP0, h⟩, fun h => h.2⟩
  rw [hset]
  haveI : IsSplittingField F (IntermediateField.adjoin F (P.rootSet E)) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  exact ⟨IsSplittingField.finiteDimensional _ P, Normal.of_isSplittingField P⟩

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
    ∃ (u : (PadicAlgCl q)ˣ) (_ : (u : PadicAlgCl q) = padicEmbedding q ζ)
      (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
      (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
      (_ : ∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
      (π : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ) (_ : ((π : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q))
      (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
      (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
      (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))),
      ((fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
        - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
            (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul π))
        ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) ∧
      continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩ ≠ 0 := by
  classical
  have hq : (q : ℕ).Prime := Fact.out
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hq1 : 1 < (q : ℕ) := hq.one_lt
  have hm : 0 < (q : ℕ) ^ p - 1 := by
    have : 1 < (q : ℕ) ^ p := Nat.one_lt_pow hp.ne_zero hq1
    omega
  have hndvd : ¬ (q : ℕ) ∣ (q : ℕ) ^ p - 1 := by
    intro h
    have h1 : (q : ℕ) ∣ (q : ℕ) ^ p := dvd_pow_self (q : ℕ) hp.ne_zero
    have : (q : ℕ) ∣ (q : ℕ) ^ p - ((q : ℕ) ^ p - 1) := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self (by omega)] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hcop : (q : ℕ).Coprime ((q : ℕ) ^ p - 1) := (Nat.Prime.coprime_iff_not_dvd hq).2 hndvd

  let Ω := PadicAlgCl (q : ℕ)
  let G := Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω
  let S : Set Ω := {x : Ω | x ^ ((q : ℕ) ^ p - 1) = 1}
  let L₀ : IntermediateField ℚ_[(q : ℕ)] Ω := IntermediateField.adjoin ℚ_[(q : ℕ)] S
  let r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := localGaloisToGlobal (q : ℕ)
  let Mμ : Rep (ZMod p) (primeLocalGaloisGroup q) := ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))
  haveI : NeZero (((q : ℕ) ^ p - 1 : ℕ) : Ω) := ⟨by exact_mod_cast hm.ne'⟩
  haveI : IsGalois ℚ_[(q : ℕ)] Ω := IsAlgClosure.isGalois _ _

  obtain ⟨hFD, hNormal⟩ := fd_normal_adjoin_rootsOfUnity_aux ℚ_[(q : ℕ)] Ω ((q : ℕ) ^ p - 1) hm
  haveI : FiniteDimensional ℚ_[(q : ℕ)] L₀ := hFD
  haveI : Normal ℚ_[(q : ℕ)] L₀ := hNormal
  haveI : IsGalois ℚ_[(q : ℕ)] L₀ := IsGalois.mk

  obtain ⟨ζ₀, hζ₀'⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ((q : ℕ) ^ p - 1) Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hm).ne')
  have hζ₀ : IsPrimitiveRoot ζ₀ ((q : ℕ) ^ p - 1) := (Polynomial.isRoot_cyclotomic_iff).1 hζ₀'
  have hζL : ζ₀ ∈ L₀ := IntermediateField.subset_adjoin _ _ hζ₀.pow_eq_one

  let K : IntermediateField ℚ_[(q : ℕ)] Ω := ⊥
  have hfinK : Module.finrank ℚ_[(q : ℕ)] K = 1 := IntermediateField.finrank_bot
  obtain ⟨e, f, -, -, -, hcardK, hef⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw (q : ℕ) K
  have hf1 : f = 1 := by
    rw [hfinK] at hef
    exact Nat.dvd_one.1 (Dvd.intro_left e hef)
  rw [hf1, pow_one] at hcardK
  obtain ⟨a, -, hcarda, hroot⟩ :=
    ExtCitation.LocalLevel.aeval_pow_card_residueField_minpoly_eq_zero (q : ℕ) K ((q : ℕ) ^ p - 1) hndvd ζ₀ hζ₀
  have ha1 : a = 1 := by
    rw [hcardK] at hcarda
    have h2 : (q : ℕ) ^ 1 = (q : ℕ) ^ a := by rw [pow_one]; exact hcarda
    exact (Nat.pow_right_injective hq.two_le h2).symm
  rw [ha1, pow_one] at hroot
  have hroot' : Polynomial.aeval (ζ₀ ^ (q : ℕ)) (minpoly ℚ_[(q : ℕ)] ζ₀) = 0 := by
    have h := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero
      (minpoly.dvd_map_of_isScalarTower ℚ_[(q : ℕ)] K ζ₀) hroot
    rwa [Polynomial.aeval_map_algebraMap] at h
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow (F := ℚ_[(q : ℕ)]) (E := Ω)
    ((q : ℕ) ^ p - 1) hm ζ₀ hζ₀ (q : ℕ) hcop hroot'
  have hfinφ : IsOfFinOrder φ := isOfFinOrder_of_finite φ

  have hcarrier : ∀ x : Ω, x ∈ IntermediateField.adjoin K S ↔ x ∈ L₀ := by
    intro x
    constructor
    · intro hx
      have hle : IntermediateField.adjoin K S ≤ IntermediateField.extendScalars (F := K) (E := L₀) bot_le :=
        IntermediateField.adjoin_le_iff.2
          (fun y hy => (IntermediateField.mem_extendScalars _).2 (IntermediateField.subset_adjoin _ _ hy))
      exact (IntermediateField.mem_extendScalars _).1 (hle hx)
    · intro hx
      have hle : L₀ ≤ (IntermediateField.adjoin K S).restrictScalars ℚ_[(q : ℕ)] :=
        IntermediateField.adjoin_le_iff.2 (fun y hy => IntermediateField.subset_adjoin K S hy)
      exact hle hx
  have hordq : orderOf (((q : ℕ) : ℕ) : ZMod ((q : ℕ) ^ p - 1)) = p := by
    rw [← ZMod.coe_unitOfCoprime (q : ℕ) hcop, orderOf_units]
    exact orderOf_unitOfCoprime_pow_sub_one (q : ℕ) p hq1 hp.pos hcop
  have hfinrank : Module.finrank ℚ_[(q : ℕ)] L₀ = p := by
    have h1 := IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf (q : ℕ) K p hp.pos
    rw [hcardK, hordq] at h1
    have h3 : (IntermediateField.adjoin K S).restrictScalars ℚ_[(q : ℕ)] = L₀ :=
      IntermediateField.ext (fun x => hcarrier x)
    have h4 : Module.finrank ℚ_[(q : ℕ)] ((IntermediateField.adjoin K S).restrictScalars ℚ_[(q : ℕ)])
        = Module.finrank ℚ_[(q : ℕ)] L₀ := by rw [h3]
    rw [← h4]
    change Module.finrank ℚ_[(q : ℕ)] (IntermediateField.adjoin K S) = p
    rw [← Module.finrank_mul_finrank ℚ_[(q : ℕ)] K (IntermediateField.adjoin K S), hfinK, one_mul, h1]
  have hcardG : Nat.card (L₀ ≃ₐ[ℚ_[(q : ℕ)]] L₀) = p := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]

  let x₀ : L₀ := ⟨ζ₀, hζL⟩
  have hφpow : ∀ i : ℕ, (((φ ^ i) x₀ : L₀) : Ω) = ζ₀ ^ ((q : ℕ) ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, AlgEquiv.one_apply, pow_zero, pow_one]
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, hφ _ (by rw [ih, ← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]),
        ih, ← pow_mul, ← pow_succ]
  have hord_le : p ≤ orderOf φ := by
    have h1 : (((φ ^ orderOf φ) x₀ : L₀) : Ω) = ζ₀ := by rw [pow_orderOf_eq_one, AlgEquiv.one_apply]
    rw [hφpow] at h1
    have h2 : ((q : ℕ) : ZMod ((q : ℕ) ^ p - 1)) ^ orderOf φ = 1 := by
      have hle : 1 ≤ (q : ℕ) ^ orderOf φ := Nat.one_le_pow _ _ hq.pos
      have h3 : ζ₀ ^ ((q : ℕ) ^ orderOf φ - 1) = 1 := by
        have h4 : ζ₀ ^ ((q : ℕ) ^ orderOf φ - 1) * ζ₀ = 1 * ζ₀ := by
          rw [one_mul, ← pow_succ, Nat.sub_add_cancel hle, h1]
        exact mul_right_cancel₀ (hζ₀.ne_zero hm.ne') h4
      rw [hζ₀.pow_eq_one_iff_dvd] at h3
      have h6 : ((((q : ℕ) ^ orderOf φ - 1 : ℕ)) : ZMod ((q : ℕ) ^ p - 1)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 h3
      have := congrArg (fun w : ZMod ((q : ℕ) ^ p - 1) => w + 1) h6
      simp only [zero_add] at this
      rw [← Nat.cast_pow, ← this, Nat.cast_sub hle, Nat.cast_one, sub_add_cancel]
    have h7 := orderOf_dvd_of_pow_eq_one h2
    rw [hordq] at h7
    exact Nat.le_of_dvd (orderOf_pos φ) h7
  have htop : Subgroup.zpowers φ = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hcardG]
    exact hord_le
  have hs : ∀ σ, σ ∈ Subgroup.zpowers φ := fun σ => by rw [htop]; exact Subgroup.mem_top σ
  have hordφ : orderOf φ = p := by rw [orderOf_eq_card_of_forall_mem_zpowers hs, hcardG]

  have hq0 : ((q : ℕ) : ℚ_[(q : ℕ)]) ≠ 0 := by exact_mod_cast hq.ne_zero
  let aK : ℚ_[(q : ℕ)]ˣ := Units.mk0 ((q : ℕ) : ℚ_[(q : ℕ)]) hq0
  let π : L₀ˣ := Units.map (algebraMap ℚ_[(q : ℕ)] L₀).toMonoidHom aK
  have hπval : (π : L₀) = algebraMap ℚ_[(q : ℕ)] L₀ ((q : ℕ) : ℚ_[(q : ℕ)]) := rfl
  have hπ : ((π : L₀) : Ω) = ((q : ℕ) : Ω) := by
    rw [hπval, IntermediateField.coe_algebraMap_apply, map_natCast]

  have hιζ : IsPrimitiveRoot (padicEmbedding (q : ℕ) ζ) p :=
    hζ.map_of_injective (padicEmbedding (q : ℕ) : AlgebraicClosure ℚ →+* Ω).injective
  have hιζu : IsUnit (padicEmbedding (q : ℕ) ζ) := hιζ.isUnit hp.ne_zero
  let u : Ωˣ := hιζu.unit
  have hu : (u : Ω) = padicEmbedding (q : ℕ) ζ := hιζu.unit_spec
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
    simp [IsUnit.unit_spec] at this
    exact this

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
  obtain ⟨FL, hFL, hUL⟩ := hlevel L₀ inferInstance
  have hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : G, r σ ∈ F.fixingSubgroup → σ ∈ L₀.fixingSubgroup := ⟨FL, hFL, hUL⟩

  let Lg : G → ℕ := fun σ => cyclicLog φ hs hfinφ (AlgEquiv.restrictNormalHom L₀ σ)
  let χ : G → ℤ := fun σ => (Lg σ : ℤ)
  have hLpow : ∀ σ, φ ^ (Lg σ) = AlgEquiv.restrictNormalHom L₀ σ := by
    intro σ
    have e1 := (finEquivZPowers hfinφ).apply_symm_apply ⟨AlgEquiv.restrictNormalHom L₀ σ, hs _⟩
    rw [finEquivZPowers_apply] at e1
    exact congrArg Subtype.val e1
  have hLlt : ∀ σ, Lg σ < p := fun σ => by rw [← hordφ]; exact Fin.is_lt _
  have hrestr1 : ∀ s : G, AlgEquiv.restrictNormalHom L₀ s = 1 ↔ s ∈ L₀.fixingSubgroup := by
    intro s
    rw [← IntermediateField.restrictNormalHom_ker L₀, MonoidHom.mem_ker]
  have hLg_one : ∀ σ, AlgEquiv.restrictNormalHom L₀ σ = 1 → Lg σ = 0 := by
    intro σ h1
    have h2 : φ ^ (Lg σ) = 1 := by rw [hLpow, h1]
    have h3 : orderOf φ ∣ Lg σ := orderOf_dvd_of_pow_eq_one h2
    rw [hordφ] at h3
    exact Nat.eq_zero_of_dvd_of_lt h3 (hLlt σ)
  have hχlc : IsLevelConstant₁ r χ := by
    refine ⟨FL, hFL, fun g s hs' => ?_⟩
    have h1 : AlgEquiv.restrictNormalHom L₀ s = 1 := (hrestr1 s).2 (hUL s hs')
    show ((Lg (g * s) : ℕ) : ℤ) = (Lg g : ℤ)
    congr 1
    show cyclicLog φ hs hfinφ (AlgEquiv.restrictNormalHom L₀ (g * s)) = cyclicLog φ hs hfinφ (AlgEquiv.restrictNormalHom L₀ g)
    rw [map_mul, h1, mul_one]
  have hχ : ∀ σ τ : G, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ) := by
    intro σ τ
    have hmod : Lg (σ * τ) ≡ Lg σ + Lg τ [MOD orderOf φ] := by
      rw [← pow_eq_pow_iff_modEq, pow_add, hLpow, hLpow, hLpow, map_mul]
    rw [hordφ] at hmod
    have h := (Nat.modEq_iff_dvd.1 hmod)
    push_cast at h
    exact h
  have hKχ : ∀ σ : G, σ ∈ L₀.fixingSubgroup ↔ (p : ℤ) ∣ χ σ := by
    intro σ
    constructor
    · intro h
      show (p : ℤ) ∣ (Lg σ : ℤ)
      rw [hLg_one σ ((hrestr1 σ).2 h)]
      simp
    · intro h
      change (p : ℤ) ∣ (Lg σ : ℤ) at h
      have h' : p ∣ Lg σ := Int.natCast_dvd_natCast.1 h
      have h0 : Lg σ = 0 := Nat.eq_zero_of_dvd_of_lt h' (hLlt σ)
      rw [← hrestr1, ← hLpow, h0, pow_zero]
  have hsχ : ∀ σ : G, (p : ℤ) ∣ χ σ - (cyclicLog φ hs hfinφ (AlgEquiv.restrictNormalHom L₀ σ) : ℤ) := by
    intro σ
    show (p : ℤ) ∣ (Lg σ : ℤ) - (Lg σ : ℤ)
    simp

  obtain ⟨α0, hα0⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : Ω) hp.pos
  have hα0ne : α0 ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hα0
    exact (Nat.cast_ne_zero.2 hq.ne_zero) hα0.symm
  let α : Ωˣ := Units.mk0 α0 hα0ne
  have hα : algebraMap ℚ_[(q : ℕ)] Ω (aK : ℚ_[(q : ℕ)]) = (α : Ω) ^ p := by
    change algebraMap ℚ_[(q : ℕ)] Ω ((q : ℕ) : ℚ_[(q : ℕ)]) = α0 ^ p
    rw [map_natCast, hα0]
  let cW : G × G → Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω := fun g =>
    (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
      ((χ g.1) • (Kummer.kummerRep ℚ_[(q : ℕ)] Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
  let infl : G × G → Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω :=
    unitsInflate₂ L₀ (carryFun φ hs hfinφ (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) (Additive.ofMul π))
  have hcong : (fun g => cW g - infl g) ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) :=
    groupCohomology.smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
      (K := ℚ_[(q : ℕ)]) (Ω := Ω) p r hlevel χ hχlc hχ L₀ hKχ φ hs hfinφ hsχ aK α hα

  have hπinv : (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀).ρ φ (Additive.ofMul π) = Additive.ofMul π := by
    apply (Additive.toMul (α := L₀ˣ)).injective
    apply Units.ext
    change φ (π : L₀) = (π : L₀)
    rw [hπval]
    exact φ.commutes _
  have hcarry_cocy : carryFun φ hs hfinφ (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) (Additive.ofMul π)
      ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) :=
    groupCohomology.carryFun_mem_cocycles2 φ hs hfinφ (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀)
      (Additive.ofMul π) hπinv
  have hinfl : infl ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) :=
    groupCohomology.unitsInflate2_mem_levelCocycles2 r L₀ hL hcarry_cocy
  have hsmΩ : ∀ mm : Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ s : G, r s ∈ F.fixingSubgroup → (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω).ρ s mm = mm := by
    intro mm
    haveI : Algebra.IsAlgebraic ℚ_[(q : ℕ)] Ω := inferInstance
    obtain ⟨xm, hxm⟩ : ∃ xm : Ω, xm = ((Additive.toMul (α := Ωˣ) mm : Ωˣ) : Ω) := ⟨_, rfl⟩
    haveI : FiniteDimensional ℚ_[(q : ℕ)] (IntermediateField.adjoin ℚ_[(q : ℕ)] {xm}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral xm)
    obtain ⟨F, hF, hUF⟩ := hlevel (IntermediateField.adjoin ℚ_[(q : ℕ)] {xm}) inferInstance
    refine ⟨F, hF, fun s hs' => ?_⟩
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ s).1 (hUF s hs') xm
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton xm))
    apply (Additive.toMul (α := Ωˣ)).injective
    apply Units.ext
    rw [hxm] at hfix
    exact hfix
  have hcb_le := groupCohomology.levelCoboundaries2_le_levelCocycles2 r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) hsmΩ
  have hcW : cW ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) := by
    have e1 : cW = (fun g => cW g - infl g) + infl := by
      funext g
      simp only [Pi.add_apply, sub_add_cancel]
    rw [e1]
    exact Submodule.add_mem _ (hcb_le hcong) hinfl

  let tg : G × G → rootsOfUnity p Ω := fun g =>
    Additive.toMul ((χ g.1) • (Kummer.kummerRep ℚ_[(q : ℕ)] Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
  have htg : ∀ g, ((tg g : Ωˣ)) ^ p = 1 := fun g => (mem_rootsOfUnity _ _).1 (tg g).2
  have hcW_tg : ∀ g, cW g = Additive.ofMul ((tg g : Ωˣ)) := fun g => rfl
  obtain ⟨z, hz_spec, -⟩ := IsPrimitiveRoot.existsUnique_eq_pow_val huprim (fun g => (tg g : Ωˣ)) htg
  let ψh : ZMod p →+ Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω :=
    { toFun := fun c => Additive.ofMul (u ^ c.val)
      map_zero' := by rw [ZMod.val_zero, pow_zero]; rfl
      map_add' := fun c d => by rw [pow_val_add_aux u hup]; rfl }
  have hψh : ∀ c : ZMod p, ψh c = Additive.ofMul (u ^ c.val) := fun _ => rfl
  have hψinj : Function.Injective ψh := by
    intro c d h
    rw [hψh, hψh] at h
    exact pow_val_injective_aux u huprim (Additive.ofMul.injective h)
  have hψρ : ∀ (g : G) (c : ZMod p),
      (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω).ρ g (ψh c) = ψh (Mμ.ρ g c) := by
    intro g c
    apply (Additive.toMul (α := Ωˣ)).injective
    apply Units.ext
    change (show Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω from g) ((u ^ c.val : Ωˣ) : Ω)
      = ((u ^ ((((cycloChar p).comp (primeLocalToGlobal q)) g : ZMod p) * c).val : Ωˣ) : Ω)
    rw [pow_val_mul_aux u hup, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      map_pow, hsmul g]
    rfl
  have hzW : ∀ g, cW g = ψh (z g) := fun g => by rw [hcW_tg, hz_spec g, hψh]
  have hz_cocy : z ∈ cocycles₂ Mμ := by
    refine (mem_cocycles₂_iff (A := Mμ) z).2 (fun g h j => ?_)
    have e1 := (mem_cocycles₂_iff cW).1 hcW.1 g h j
    rw [hzW, hzW, hzW, hzW, hψρ, ← map_add, ← map_add] at e1
    exact hψinj e1
  have hz_lc : IsLevelConstant₂ (primeLocalToGlobal q) z := by
    obtain ⟨F, hF, hF2⟩ := hcW.2
    refine ⟨F, hF, fun g g' s s' hs1 hs2 => hψinj ?_⟩
    rw [← hzW, ← hzW]
    exact hF2 g g' s s' hs1 hs2
  have hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) Mμ := ⟨hz_cocy, hz_lc⟩

  refine ⟨u, hu, φ, hs, hfinφ, hφ, π, hπ, hNormal, z, hz, ?_, ?_⟩
  · show (fun g : G × G => ψh (z g) - infl g) ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω)
    have key : (fun g : G × G => ψh (z g) - infl g) = fun g => cW g - infl g := by
      funext g
      rw [hzW g]
    rw [key]
    exact hcong
  · intro h0
    rw [continuousH2π_eq_zero_iff] at h0
    obtain ⟨b, hb_lc, hb⟩ := (mem_levelCoboundaries₂_iff (primeLocalToGlobal q) Mμ z).1 h0

    have hcWcb : cW ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) := by
      refine (mem_levelCoboundaries₂_iff r _ _).2 ⟨fun g => ψh (b g), ?_, ?_⟩
      · obtain ⟨F, hF, hF1⟩ := hb_lc
        exact ⟨F, hF, fun g s hs' => congrArg ψh (hF1 g s hs')⟩
      · funext g
        obtain ⟨g₁, g₂⟩ := g
        have e2 := congrFun hb (g₁, g₂)
        rw [d₁₂_hom_apply] at e2 ⊢
        rw [hzW]
        calc (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω).ρ g₁ (ψh (b g₂)) - ψh (b (g₁ * g₂)) + ψh (b g₁)
            = ψh (Mμ.ρ g₁ (b g₂) - b (g₁ * g₂) + b g₁) := by rw [map_add, map_sub, hψρ]
          _ = ψh (z (g₁, g₂)) := congrArg ψh e2
    have hinfl_cb : infl ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] Ω) := by
      have e3 : infl = cW - (fun g => cW g - infl g) := by
        funext g
        simp only [Pi.sub_apply, sub_sub_cancel]
      rw [e3]
      exact Submodule.sub_mem _ hcWcb hcong
    have hcarry_cb := groupCohomology.mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 r hopen L₀
      hcarry_cocy hinfl_cb
    have hH2 : (H2π (Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀)).hom
        ⟨carryFun φ hs hfinφ (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) (Additive.ofMul π), hcarry_cocy⟩ = 0 :=
      (H2π_eq_zero_iff _).2 hcarry_cb
    obtain ⟨bb, hbb⟩ := (groupCohomology.carry_H2pi_eq_zero_iff φ hs hfinφ
      (A := Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀) (Additive.ofMul π) hπinv hcarry_cocy).1 hH2
    rw [hordφ] at hbb

    let vΩ : Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀ →+ Additive Ωˣ :=
      { toFun := fun x => Additive.ofMul (Units.map (algebraMap L₀ Ω).toMonoidHom (Additive.toMul (α := L₀ˣ) x))
        map_zero' := congrArg Additive.ofMul (map_one (Units.map (algebraMap L₀ Ω).toMonoidHom))
        map_add' := fun x y => congrArg Additive.ofMul
          (map_mul (Units.map (algebraMap L₀ Ω).toMonoidHom) (Additive.toMul (α := L₀ˣ) x) (Additive.toMul (α := L₀ˣ) y)) }
    have hvΩ : ∀ x : Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀,
        ((Additive.toMul (vΩ x) : Ωˣ) : Ω) = (((Additive.toMul (α := L₀ˣ) x : L₀ˣ) : L₀) : Ω) := fun _ => rfl
    obtain ⟨bL, hbL⟩ : ∃ bL : L₀, bL = ((Additive.toMul (α := L₀ˣ) bb : L₀ˣ) : L₀) := ⟨_, rfl⟩
    have hbL0 : bL ≠ 0 := by rw [hbL]; exact Units.ne_zero _
    have hρread : ∀ i : ℕ, ((Additive.toMul (vΩ ((Rep.ofAlgebraAutOnUnits ℚ_[(q : ℕ)] L₀).ρ (φ ^ i) bb)) : Ωˣ) : Ω)
        = (((φ ^ i) bL : L₀) : Ω) := fun i => by rw [hvΩ, hbL]; rfl
    have e4 := congrArg vΩ hbb
    rw [map_sum] at e4
    have e5 := congrArg (fun y : Additive Ωˣ => ((Additive.toMul y : Ωˣ) : Ω)) e4
    simp only [toMul_sum, Units.coe_prod, hρread] at e5

    have e6 : ((Additive.toMul (vΩ (Additive.ofMul π)) : Ωˣ) : Ω) = ((q : ℕ) : Ω) := by rw [hvΩ, ← hπ]; rfl
    rw [e6] at e5

    haveI : Normal ℚ_[(q : ℕ)] Ω := inferInstance
    have hiso : ∀ σ : L₀ ≃ₐ[ℚ_[(q : ℕ)]] L₀, ∀ y : L₀, ‖((σ y : L₀) : Ω)‖ = ‖(y : Ω)‖ := by
      intro σ y
      have h1 : (σ.liftNormal Ω) ((y : Ω)) = ((σ y : L₀) : Ω) := by
        have := AlgEquiv.liftNormal_commutes σ Ω y
        rwa [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply] at this
      have h2 := nnnorm_padicAlgCl_algEquiv (q : ℕ) (σ.liftNormal Ω) (y : Ω)
      rw [h1] at h2
      rw [← coe_nnnorm, ← coe_nnnorm, h2]
    have e7 : ‖((q : ℕ) : Ω)‖ = ‖(bL : Ω)‖ ^ p := by
      rw [← e5, norm_prod]
      simp only [hiso, Finset.prod_const, Finset.card_range]

    have e8 : ‖((q : ℕ) : Ω)‖ = ((q : ℕ) : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[(q : ℕ)] Ω), PadicAlgCl.norm_extends, Padic.norm_p]

    have hbLmem : (bL : Ω) ∈ IntermediateField.adjoin K S := (hcarrier _).2 bL.2
    obtain ⟨y, hy⟩ := IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic (q : ℕ) K p hp.pos
      ⟨(bL : Ω), hbLmem⟩ (by
        intro h
        apply hbL0
        have := congrArg Subtype.val h
        exact Subtype.ext this)
    obtain ⟨y0, hy0⟩ := IntermediateField.mem_bot.1 y.2
    change ‖(bL : Ω)‖ = ‖((y : K) : Ω)‖ at hy
    rw [← hy0, PadicAlgCl.norm_extends] at hy
    have hy0ne : y0 ≠ 0 := by
      intro h
      rw [h, norm_zero, norm_eq_zero] at hy
      exact hbL0 (Subtype.ext hy)
    rw [Padic.norm_eq_zpow_neg_valuation hy0ne] at hy

    rw [e8, hy, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at e7
    have hqR : (1 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast hq1
    have e9 : (-1 : ℤ) = -y0.valuation * (p : ℤ) := zpow_right_injective₀ (by positivity) hqR.ne' e7
    have e10 : (p : ℤ) * y0.valuation = 1 := by linarith
    have e11 : (p : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) e10
    have : p = 1 := by exact_mod_cast e11
    exact hp.one_lt.ne' this

end S_groupCohomology_exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness
end P2MW
export P2MW.S_groupCohomology_exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness (solution)
