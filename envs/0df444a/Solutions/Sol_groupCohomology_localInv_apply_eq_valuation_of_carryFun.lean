-- Prove2me | solution 1 for groupCohomology.localInv_apply_eq_valuation_of_carryFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7d2dedc1-a659-5406-a246-4751118140d1

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant
import Theorems.Thm_groupCohomology_isLocalInv_localInv_and_bijective
import Theorems.Thm_groupCohomology_exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness
import Theorems.Thm_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_localInv_apply_eq_valuation_of_carryFun
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory ExtCitation groupCohomology Polynomial

namespace P2M
namespace InvCarry

section CyclicLog

variable {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)

lemma cyclicLog_lt (g : G) : cyclicLog s hs hfin g < orderOf s :=
  ((finEquivZPowers hfin).symm ⟨g, hs g⟩).isLt

lemma pow_cyclicLog (g : G) : s ^ cyclicLog s hs hfin g = g := by
  have h := (finEquivZPowers hfin).apply_symm_apply ⟨g, hs g⟩
  rw [finEquivZPowers_apply] at h
  exact congrArg Subtype.val h

lemma cyclicLog_pow_of_lt {i : ℕ} (hi : i < orderOf s) : cyclicLog s hs hfin (s ^ i) = i := by
  have h := finEquivZPowers_symm_apply hfin i
  unfold cyclicLog
  have : (⟨s ^ i, hs (s ^ i)⟩ : Subgroup.zpowers s) = ⟨s ^ i, ⟨(i : ℤ), by simp⟩⟩ := rfl
  rw [this] at *
  rw [h]
  exact Nat.mod_eq_of_lt hi

lemma cyclicLog_pow (i : ℕ) : cyclicLog s hs hfin (s ^ i) = i % orderOf s := by
  have hpos : 0 < orderOf s := hfin.orderOf_pos
  rw [show s ^ i = s ^ (i % orderOf s) from (pow_mod_orderOf s i).symm]
  exact cyclicLog_pow_of_lt s hs hfin (Nat.mod_lt _ hpos)

lemma cyclicLog_mul (g h : G) :
    cyclicLog s hs hfin (g * h) = (cyclicLog s hs hfin g + cyclicLog s hs hfin h) % orderOf s := by
  conv_lhs => rw [← pow_cyclicLog s hs hfin g, ← pow_cyclicLog s hs hfin h, ← pow_add]
  exact cyclicLog_pow s hs hfin _

lemma cyclicLog_one : cyclicLog s hs hfin 1 = 0 := by
  simpa using cyclicLog_pow_of_lt s hs hfin hfin.orderOf_pos

end CyclicLog

section NormCoboundary

variable {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
variable {A : Rep ℤ G}

noncomputable def normChain (β : A) : G → A :=
  fun g => ∑ j ∈ Finset.range (cyclicLog s hs hfin g), A.ρ (s ^ j) β

include hfin in

lemma sum_Ico_period (β : A) (m : ℕ) :
    ∑ j ∈ Finset.Ico m (m + orderOf s), A.ρ (s ^ j) β
      = ∑ j ∈ Finset.range (orderOf s), A.ρ (s ^ j) β := by
  induction m with
  | zero => rw [Nat.zero_add, Finset.range_eq_Ico]
  | succ m ih =>
    have h1 : ∑ j ∈ Finset.Ico m (m + orderOf s), A.ρ (s ^ j) β
        = A.ρ (s ^ m) β + ∑ j ∈ Finset.Ico (m + 1) (m + orderOf s), A.ρ (s ^ j) β := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by have := hfin.orderOf_pos; omega)]
    have h2 : ∑ j ∈ Finset.Ico (m + 1) (m + 1 + orderOf s), A.ρ (s ^ j) β
        = (∑ j ∈ Finset.Ico (m + 1) (m + orderOf s), A.ρ (s ^ j) β) + A.ρ (s ^ (m + orderOf s)) β := by
      rw [show m + 1 + orderOf s = (m + orderOf s) + 1 by ring,
        Finset.sum_Ico_succ_top (by have := hfin.orderOf_pos; omega)]
    rw [h2, ← ih, h1, pow_add, pow_orderOf_eq_one, mul_one, add_comm]

lemma d₁₂_normChain (β : A) :
    (d₁₂ A).hom (normChain s hs hfin β)
      = carryFun s hs hfin (∑ j ∈ Finset.range (orderOf s), A.ρ (s ^ j) β) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [d₁₂_hom_apply]
  simp only [normChain, carryFun]
  set i := cyclicLog s hs hfin g with hi
  set j := cyclicLog s hs hfin h with hj
  have hi_lt : i < orderOf s := cyclicLog_lt s hs hfin g
  have hj_lt : j < orderOf s := cyclicLog_lt s hs hfin h
  have hgh : cyclicLog s hs hfin (g * h) = (i + j) % orderOf s := cyclicLog_mul s hs hfin g h

  have hgb : A.ρ g (∑ l ∈ Finset.range j, A.ρ (s ^ l) β)
      = ∑ l ∈ Finset.Ico i (i + j), A.ρ (s ^ l) β := by
    rw [map_sum (A.ρ g), Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← pow_cyclicLog s hs hfin g, ← hi, pow_add, map_mul]
    rfl
  have hsplit : ∑ l ∈ Finset.Ico i (i + j), A.ρ (s ^ l) β + ∑ l ∈ Finset.range i, A.ρ (s ^ l) β
      = ∑ l ∈ Finset.range (i + j), A.ρ (s ^ l) β := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, add_comm,
      Finset.sum_Ico_consecutive _ (Nat.zero_le i) (Nat.le_add_right i j)]
  rw [hgb, hgh]
  by_cases hc : orderOf s ≤ i + j
  · rw [if_pos hc]
    have hmod : (i + j) % orderOf s = i + j - orderOf s := by
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, sub_add_eq_add_sub, hsplit, sub_eq_iff_eq_add, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (i + j - orderOf s)) (Nat.sub_le (i + j) (orderOf s)),
      add_comm]
    have := sum_Ico_period s hfin β (i + j - orderOf s)
    rw [Nat.sub_add_cancel hc] at this
    rw [this, Finset.range_eq_Ico, Finset.range_eq_Ico]
  · rw [if_neg hc]
    have hmod : (i + j) % orderOf s = i + j := Nat.mod_eq_of_lt (by omega)
    rw [hmod, sub_add_eq_add_sub, hsplit, sub_self]

lemma carryFun_norm_mem_coboundaries₂ (β : A) :
    carryFun s hs hfin (∑ j ∈ Finset.range (orderOf s), A.ρ (s ^ j) β) ∈ coboundaries₂ A :=
  ⟨normChain s hs hfin β, d₁₂_normChain s hs hfin β⟩

include hs in

lemma sum_range_orderOf_eq_sum_univ [Fintype G] (f : G → A) :
    ∑ j ∈ Finset.range (orderOf s), f (s ^ j) = ∑ g : G, f g := by
  classical
  have hord : orderOf s = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card]
  have hinj : Set.InjOn (fun j : ℕ => s ^ j) ↑(Finset.range (orderOf s)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := (pow_inj_mod).mp hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have himg : Finset.image (fun j : ℕ => s ^ j) (Finset.range (orderOf s)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, hord]
  rw [← himg, Finset.sum_image hinj]

lemma carryFun_add (a b : A) : carryFun s hs hfin (a + b) = carryFun s hs hfin a + carryFun s hs hfin b := by
  funext p; simp only [carryFun, Pi.add_apply]; split_ifs <;> simp

lemma carryFun_zsmul (n : ℤ) (a : A) : carryFun s hs hfin (n • a) = n • carryFun s hs hfin a := by
  funext p; simp only [carryFun, Pi.smul_apply]; split_ifs <;> simp

lemma carryFun_zero : carryFun s hs hfin (0 : A) = 0 := by
  funext p; simp only [carryFun, Pi.zero_apply]; split_ifs <;> simp

end NormCoboundary

section Level

variable (q : ℕ) [Fact q.Prime]

set_option hygiene false in
local notation "Ω" => PadicAlgCl q

lemma exists_level_fixing_rootsOfUnity (N : ℕ) (hN : 0 < N) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : (Ω ≃ₐ[ℚ_[q]] Ω), localGaloisToGlobal q s ∈ F.fixingSubgroup →
        ∀ x : Ω, x ^ N = 1 → s x = x := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ : AlgebraicClosure ℚ, IsPrimitiveRoot ξ N := HasEnoughRootsOfUnity.prim
  refine ⟨IntermediateField.adjoin ℚ {ξ₀}, ?_, ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional (hξ₀.isIntegral hN).tower_top
  · intro s hs x hx
    have hfix : localGaloisToGlobal q s ξ₀ = ξ₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs ξ₀ (IntermediateField.mem_adjoin_simple_self ℚ ξ₀)
    have hsξ : s (padicEmbedding q ξ₀) = padicEmbedding q ξ₀ := by
      rw [← padicEmbedding_localGaloisToGlobal, hfix]
    have hprim : IsPrimitiveRoot (padicEmbedding q ξ₀) N :=
      hξ₀.map_of_injective (padicEmbedding q).toRingHom.injective
    obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hx
    rw [map_pow, hsξ]

variable (L : IntermediateField ℚ_[q] Ω) [Normal ℚ_[q] L]

lemma restrictNormalHom_eq_one_of_forall {S : Set Ω} (hLS : L ≤ IntermediateField.adjoin ℚ_[q] S)
    (s : Ω ≃ₐ[ℚ_[q]] Ω) (hs : ∀ x ∈ S, s x = x) : AlgEquiv.restrictNormalHom L s = 1 := by
  have hle : IntermediateField.adjoin ℚ_[q] S ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro g ⟨k, rfl⟩
    change (s ^ k) x = x
    have h1 : s x = x := hs x hx
    have hsymm : s.symm x = x := by
      conv_lhs => rw [← h1]
      exact s.symm_apply_apply x
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, h1]; exact ih
    | pred k ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hsymm]; exact ih
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  have hy : s (y : Ω) = y := by
    have hmem := hle (hLS y.2)
    rw [IntermediateField.mem_fixedField_iff] at hmem
    exact hmem s (Subgroup.mem_zpowers s)
  change ((AlgEquiv.restrictNormal s L y : L) : Ω) = y
  have := AlgEquiv.restrictNormal_commutes s L y
  simp only [IntermediateField.algebraMap_apply] at this
  rw [this, hy]

lemma isLevelConstant₁_unitsInflate₁ {N : ℕ} (hN : 0 < N)
    (hLS : L ≤ IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ N = 1})
    (b : (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ) :
    IsLevelConstant₁ (localGaloisToGlobal q) (unitsInflate₁ L b) := by
  obtain ⟨F, hF, hFfix⟩ := exists_level_fixing_rootsOfUnity q N hN
  refine ⟨F, hF, fun g s hs => ?_⟩
  have h1 : AlgEquiv.restrictNormalHom L s = 1 :=
    restrictNormalHom_eq_one_of_forall q L hLS s (fun x hx => hFfix s hs x hx)
  simp only [unitsInflate₁_apply, map_mul, h1, mul_one]

lemma unitsInflate₂_d₁₂ (b : (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ) :
    unitsInflate₂ L ((d₁₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] L)).hom b)
      = (d₁₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] Ω)).hom (unitsInflate₁ L b) := by
  funext στ
  obtain ⟨σ, τ⟩ := στ
  rw [d₁₂_hom_apply, unitsInflate₂_apply, d₁₂_hom_apply]
  change Additive.ofMul (Units.map (↑(algebraMap L (PadicAlgCl q))) (Additive.toMul
      ((Additive.ofMul ((AlgEquiv.restrictNormalHom L σ) • Additive.toMul (b (AlgEquiv.restrictNormalHom L τ))) -
          b (AlgEquiv.restrictNormalHom L σ * AlgEquiv.restrictNormalHom L τ) +
          b (AlgEquiv.restrictNormalHom L σ) : Additive (L)ˣ)))) =
      (Additive.ofMul (σ • Additive.toMul (unitsInflate₁ L b τ)) - unitsInflate₁ L b (σ * τ) +
        unitsInflate₁ L b σ : Additive (PadicAlgCl q)ˣ)
  simp only [map_mul, toMul_sub, toMul_add, toMul_ofMul, ofMul_mul, unitsInflate₁_apply,
    div_eq_mul_inv, map_inv, ofMul_inv, RingHom.toMonoidHom_eq_coe]
  congr 3
  apply Units.ext
  rw [Units.coe_map, AlgEquiv.smul_units_def, AlgEquiv.smul_units_def, Units.coe_map, Units.coe_map,
    Units.coe_map]
  exact AlgEquiv.restrictNormal_commutes σ L _

lemma unitsInflate₂_mem_levelCoboundaries₂_of_mem_coboundaries₂ {N : ℕ} (hN : 0 < N)
    (hLS : L ≤ IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ N = 1})
    {c : (L ≃ₐ[ℚ_[q]] L) × (L ≃ₐ[ℚ_[q]] L) → Additive (L)ˣ}
    (hc : c ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] L)) :
    unitsInflate₂ L c ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] Ω) := by
  obtain ⟨b, rfl⟩ := hc
  exact (mem_levelCoboundaries₂_iff _ _ _).mpr
    ⟨unitsInflate₁ L b, isLevelConstant₁_unitsInflate₁ q L hN hLS b, (unitsInflate₂_d₁₂ q L b).symm⟩

omit [Normal ℚ_[q] L] in

lemma algEquiv_eq_of_frobenius {N : ℕ} (hL : L = IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ N = 1})
    (φ φ' : L ≃ₐ[ℚ_[q]] L)
    (hφ : ∀ x : L, (x : Ω) ^ N = 1 → (φ x : Ω) = (x : Ω) ^ q)
    (hφ' : ∀ x : L, (x : Ω) ^ N = 1 → (φ' x : Ω) = (x : Ω) ^ q) : φ = φ' := by
  apply AlgEquiv.coe_algHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[q] hL fun x hx => ?_
  apply Subtype.ext
  change ((φ ⟨x, _⟩ : L) : Ω) = ((φ' ⟨x, _⟩ : L) : Ω)
  have hx' : x ^ N = 1 := hx
  rw [hφ _ hx', hφ' _ hx']

end Level

section CycloLayer

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

lemma finiteDimensional_adjoin_setOf_pow_eq_one {K : Type*} [Field K] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    FiniteDimensional K (IntermediateField.adjoin K {x : Ω | x ^ n = 1}) := by
  haveI : Finite ({x : Ω | x ^ n = 1} : Set Ω) := (finite_setOf_pow_eq_one q n hn).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp only [eval₂_sub, eval₂_X_pow, map_one, eval₂_one, sub_eq_zero]
  exact hx

lemma normal_adjoin_setOf_pow_eq_one {K : Type*} [Field K] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    Normal K (IntermediateField.adjoin K {x : Ω | x ^ n = 1}) := by
  rw [setOf_pow_eq_one_eq_rootSet q (K := K) n hn]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := (X ^ n - C 1 : K[X]))
    (IsAlgClosed.splits _)
  exact Normal.of_isSplittingField (X ^ n - C 1 : K[X])

lemma isGalois_adjoin_setOf_pow_eq_one {K : Type*} [Field K] [Algebra K Ω] [CharZero K] (n : ℕ) (hn : 0 < n) :
    IsGalois K (IntermediateField.adjoin K {x : Ω | x ^ n = 1}) := by
  haveI := finiteDimensional_adjoin_setOf_pow_eq_one q (K := K) n hn
  haveI := normal_adjoin_setOf_pow_eq_one q (K := K) n hn
  haveI : PerfectField K := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable K (IntermediateField.adjoin K {x : Ω | x ^ n = 1}) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact IsGalois.mk

lemma exists_prod_algEquiv_eq_of_norm_eq_one (N : ℕ) (hN : 0 < N) (u : ℚ_[q]) (hu : ‖u‖ = 1)
    [FiniteDimensional ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ (q ^ N - 1) = 1})] :
    ∃ w : IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ (q ^ N - 1) = 1},
      ∏ g : ((IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ (q ^ N - 1) = 1}) ≃ₐ[ℚ_[q]]
              (IntermediateField.adjoin ℚ_[q] {x : Ω | x ^ (q ^ N - 1) = 1})), g w
        = algebraMap ℚ_[q] _ u := by
  have hn : 0 < q ^ N - 1 := by
    have h1 : 1 < q ^ N := Nat.one_lt_pow hN.ne' (Fact.out : q.Prime).one_lt
    omega
  set S : Set Ω := {x : Ω | x ^ (q ^ N - 1) = 1} with hS
  set L : IntermediateField ℚ_[q] Ω := IntermediateField.adjoin ℚ_[q] S with hLdef
  set K₀ : IntermediateField ℚ_[q] Ω := ⊥ with hK₀
  set L₀ : IntermediateField K₀ Ω := IntermediateField.adjoin K₀ S with hL₀
  haveI hfd₀ : FiniteDimensional K₀ L₀ := finiteDimensional_adjoin_setOf_pow_eq_one q (K := K₀) _ hn
  haveI : IsGalois K₀ L₀ := isGalois_adjoin_setOf_pow_eq_one q (K := K₀) _ hn
  haveI : IsGalois ℚ_[q] L := isGalois_adjoin_setOf_pow_eq_one q (K := ℚ_[q]) _ hn

  let u₀ : K₀ := ⟨algebraMap ℚ_[q] Ω u, IntermediateField.mem_bot.mpr ⟨u, rfl⟩⟩
  have hu₀ : ‖(u₀ : Ω)‖ = 1 := by
    change ‖algebraMap ℚ_[q] Ω u‖ = 1
    simpa using hu
  obtain ⟨w₀, hw₀⟩ :=
    IntermediateField.exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic q K₀ N hN u₀ hu₀

  have hres : IntermediateField.restrictScalars ℚ_[q] L₀ = L := by
    rw [hL₀, IntermediateField.restrictScalars_adjoin]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | hx)
      · exact (bot_le : (⊥ : IntermediateField ℚ_[q] Ω) ≤ L) hx
      · exact IntermediateField.subset_adjoin ℚ_[q] S hx
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
  let e : L₀ ≃ₐ[ℚ_[q]] L :=
    (IntermediateField.equivOfEq hres : IntermediateField.restrictScalars ℚ_[q] L₀ ≃ₐ[ℚ_[q]] L)
  refine ⟨e w₀, ?_⟩
  have hprod := Algebra.norm_eq_prod_automorphisms ℚ_[q] (e w₀)
  rw [← hprod]
  congr 1
  rw [Algebra.norm_eq_of_algEquiv]

  have htower : Algebra.norm ℚ_[q] (Algebra.norm K₀ w₀) = Algebra.norm ℚ_[q] w₀ := Algebra.norm_norm
  rw [← show Algebra.norm ℚ_[q] (w₀ : IntermediateField.restrictScalars ℚ_[q] L₀) = Algebra.norm ℚ_[q] w₀
      from rfl] at htower
  rw [← htower, hw₀]
  have hu₀' : u₀ = algebraMap ℚ_[q] K₀ u := Subtype.ext rfl
  rw [hu₀', Algebra.norm_algebraMap, IntermediateField.finrank_bot, pow_one]

end CycloLayer

section Assembly

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

set_option hygiene false in
local notation "Ω" => PadicAlgCl q
set_option hygiene false in
local notation "L" => (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
set_option hygiene false in
local notation "Λ" => (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))

omit [Fact p.Prime] in
include hζ in
lemma pow_p_eq_one_of_eq_padicEmbedding (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) :
    u ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hu, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]

noncomputable def uExp (u : (PadicAlgCl q)ˣ) (y : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p) :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Additive (PadicAlgCl q)ˣ :=
  fun g => Additive.ofMul (u ^ (y g).val)

lemma uExp_add (u : (PadicAlgCl q)ˣ) (hup : u ^ p = 1)
    (y y' : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p) :
    uExp p q u (y + y') = uExp p q u y + uExp p q u y' := by
  funext g
  simp only [uExp, Pi.add_apply, ZMod.val_add, ← ofMul_mul, ← pow_add]
  rw [← pow_eq_pow_mod _ hup]

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

end Assembly

end P2M.InvCarry

set_option hygiene false in
local notation "Lf" => (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
set_option hygiene false in
local notation "Λ" => (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))

open P2M.InvCarry in
theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (a : ℚ_[q]) (ha : a ≠ 0)
    (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ)
    (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (hφ : ∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
    (α : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ)
    (hα : ((α : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) a)
    (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
    (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (hcob : (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
        - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
            (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul α))
        ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) :
    localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩)
      = ((Padic.valuation a : ℤ) : ZMod p) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hqP : ((q : ℕ)).Prime := Fact.out
  have hN : 0 < (q : ℕ) ^ p - 1 := by
    have := Nat.one_lt_pow hp.ne' hqP.one_lt
    omega
  haveI instFD : FiniteDimensional ℚ_[q] Lf := finiteDimensional_adjoin_setOf_pow_eq_one (q : ℕ) _ hN
  have hup : u ^ p = 1 := pow_p_eq_one_of_eq_padicEmbedding p ζ hζ q u hu

  obtain ⟨u₀, hu₀, φ₀, hs₀, hfin₀, hφ₀, π, hπ, instN₀, z₀, hz₀, hcob₀, -⟩ :=
    exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness p ζ hζ q
  have eu : u = u₀ := Units.ext (hu.trans hu₀.symm)
  subst eu
  have eφ : φ = φ₀ := algEquiv_eq_of_frobenius (q : ℕ) Lf rfl φ φ₀ hφ hφ₀
  subst eφ
  have hLI := (isLocalInv_localInv_and_bijective p ζ hζ q).1
  have h0 : localInv p ζ q (continuousH2π (primeLocalToGlobal q) Λ ⟨z₀, hz₀⟩) = 1 :=
    hLI u hu φ hs₀ hfin₀ hφ₀ π hπ instN₀ z₀ hz₀ hcob₀

  set k : ℤ := Padic.valuation a with hk
  have hq0 : ((q : ℕ) : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr hqP.ne_zero
  set u₁ : ℚ_[q] := a * ((q : ℕ) : ℚ_[q]) ^ (-k) with hu₁def
  have hu₁ : ‖u₁‖ = 1 := by
    rw [hu₁def, norm_mul, norm_zpow, Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_p, inv_zpow', neg_neg, ← hk,
      ← zpow_add₀ (by exact_mod_cast hqP.ne_zero : ((q : ℕ) : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  have ha' : a = ((q : ℕ) : ℚ_[q]) ^ k * u₁ := by
    rw [hu₁def, mul_left_comm, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero, mul_one]
  have hu₁0 : u₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hu₁; exact zero_ne_one hu₁

  obtain ⟨w, hw⟩ := exists_prod_algEquiv_eq_of_norm_eq_one (q : ℕ) p hp u₁ hu₁
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Finset.prod_eq_zero (Finset.mem_univ (1 : Lf ≃ₐ[ℚ_[q]] Lf)) (map_zero _)] at hw
    exact hu₁0 ((map_eq_zero_iff _ (algebraMap ℚ_[q] Lf).injective).mp hw.symm)
  set β : (Lf)ˣ := Units.mk0 w hw0 with hβ
  set υ : (Lf)ˣ := ∏ g : (Lf ≃ₐ[ℚ_[q]] Lf), g • β with hυdef
  have hυval : (υ : Lf) = algebraMap ℚ_[q] Lf u₁ := by
    rw [hυdef, Units.coe_prod]
    exact hw

  have hπval : ((π : Lf) : Lf) = algebraMap ℚ_[q] Lf ((q : ℕ) : ℚ_[q]) := by
    apply Subtype.ext
    rw [hπ, IntermediateField.coe_algebraMap_apply, map_natCast]
  have hαval : ((α : Lf) : Lf) = algebraMap ℚ_[q] Lf a := by
    apply Subtype.ext
    rw [hα, IntermediateField.coe_algebraMap_apply]
  have hαdec : α = π ^ k * υ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hαval, hπval, hυval, ← map_zpow₀, ← map_mul, ← ha']

  have hcarry : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul α)
      = ((k • carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul π)
          + carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul υ) :
            (Lf ≃ₐ[ℚ_[q]] Lf) × (Lf ≃ₐ[ℚ_[q]] Lf) → Additive (Lf)ˣ)) := by
    have e : (Additive.ofMul α : Additive (Lf)ˣ) = k • Additive.ofMul π + Additive.ofMul υ := by
      rw [hαdec, ofMul_mul, ofMul_zpow]
    funext g
    simp only [carryFun, Pi.add_apply, Pi.smul_apply]
    split_ifs
    · exact e
    · rw [smul_zero, add_zero]
  have hυcob : carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul υ)
      ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) := by
    have key := carryFun_norm_mem_coboundaries₂ φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul β)
    have hsum : (∑ j ∈ Finset.range (orderOf φ), (Rep.ofAlgebraAutOnUnits ℚ_[q] Lf).ρ (φ ^ j) (Additive.ofMul β))
        = Additive.ofMul υ := by
      rw [hυdef, ofMul_prod]
      exact sum_range_orderOf_eq_sum_univ φ hs (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf)
        (fun g => Additive.ofMul (g • β))
    rw [hsum] at key
    exact key
  have hinflυ := unitsInflate₂_mem_levelCoboundaries₂_of_mem_coboundaries₂ (q : ℕ) Lf hN le_rfl hυcob

  set cπ := unitsInflate₂ Lf (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul π)) with hcπ
  set cα := unitsInflate₂ Lf (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul α)) with hcα
  set cυ := unitsInflate₂ Lf (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul υ)) with hcυ
  have hcαdec : cα = k • cπ + cυ := by
    rw [hcα, hcarry, hcπ, hcυ]
    refine ((unitsInflate₂ Lf).map_add _ _).trans ?_
    congr 1
    exact (unitsInflate₂ Lf).map_smul k
      (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] Lf) (Additive.ofMul π))
  set m : ℤ := 1 - k with hm
  set LC := levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) with hLC
  have hcobz : uExp p q u z - cα ∈ LC := hcob
  have hcobz₀ : uExp p q u z₀ - cπ ∈ LC := hcob₀
  have hz' : z + ((m : ZMod p)) • z₀ ∈ levelCocycles₂ (primeLocalToGlobal q) Λ :=
    add_mem hz (Submodule.smul_mem _ _ hz₀)
  have hcob' : uExp p q u (z + ((m : ZMod p)) • z₀) - cπ ∈ LC := by
    have e1 : uExp p q u (z + ((m : ZMod p)) • z₀) = uExp p q u z + m • uExp p q u z₀ := by
      rw [uExp_add _ _ _ hup, uExp_intCast_smul _ _ _ hup]
    have e2 : uExp p q u (z + ((m : ZMod p)) • z₀) - cπ
        = (uExp p q u z - cα) + cυ + m • (uExp p q u z₀ - cπ) := by
      rw [e1, hcαdec, hm]
      module
    rw [e2]
    exact add_mem (add_mem hcobz hinflυ) (LC.smul_mem m hcobz₀)
  have h1 : localInv p ζ q (continuousH2π (primeLocalToGlobal q) Λ ⟨_, hz'⟩) = 1 :=
    hLI u hu φ hs hfin hφ π hπ ‹Normal ℚ_[q] Lf› _ hz' hcob'

  have hcls : continuousH2π (primeLocalToGlobal q) Λ ⟨_, hz'⟩
      = continuousH2π (primeLocalToGlobal q) Λ ⟨z, hz⟩
        + ((m : ZMod p)) • continuousH2π (primeLocalToGlobal q) Λ ⟨z₀, hz₀⟩ := by
    rw [← map_smul, ← map_add]
    rfl
  rw [hcls, map_add, map_smul, h0, smul_eq_mul, mul_one, hm, Int.cast_sub, Int.cast_one] at h1
  linear_combination h1

end S_groupCohomology_localInv_apply_eq_valuation_of_carryFun
end P2MW
export P2MW.S_groupCohomology_localInv_apply_eq_valuation_of_carryFun (solution)
