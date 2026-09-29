-- Prove2me | solution 1 for groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c01ebd0b-ebd8-58c6-8da8-13528869acf1

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Theorems.Thm_ExtCitation_exists_tame_generator_at_level
import Theorems.Thm_ExtCitation_finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep
import Theorems.Thm_groupCohomology_finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hne : (q : ℕ) ≠ p)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (adm₁ : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm₁]
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm₁
      ≤ finrank (ZMod p) M.ρ.invariants
        + finrank (ZMod p)
            (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hqf : Fact (q : ℕ).Prime := ⟨q.2⟩
  set r := primeLocalToGlobal q with hr
  set χ : primeLocalGaloisGroup q →* (ZMod p)ˣ := (cycloChar p).comp r with hχdef
  let I : Subgroup (primeLocalGaloisGroup q) := ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap r
  haveI hIN : I.Normal := ExtCitation.inertiaPullback_normal q

  haveI : Finite M := Module.finite_of_finite (ZMod p)
  choose Fm hFm using hsm
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ m : M, Fm m
  haveI : ∀ m : M, FiniteDimensional ℚ (Fm m) := fun m => (hFm m).1
  haveI hLfin : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_iSup_of_finite
  have hUL : ∀ g ∈ (L.fixingSubgroup).comap r, M.ρ g = 1 := by
    intro g hg
    refine LinearMap.ext fun m => ?_
    exact (hFm m).2 g (IntermediateField.fixingSubgroup_antitone (le_iSup Fm m) (Subgroup.mem_comap.1 hg))

  let K₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {primRoot p}
  have hint : IsIntegral ℚ (primRoot p) :=
    IsIntegral.of_pow (Fact.out : p.Prime).pos
      (by rw [(isPrimitiveRoot_primRoot p).pow_eq_one]; exact isIntegral_one)
  haveI : FiniteDimensional ℚ K₀ := IntermediateField.adjoin.finiteDimensional hint
  let F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ K₀
  haveI : FiniteDimensional ℚ F₀ := IntermediateField.finiteDimensional_sup L K₀

  obtain ⟨φ, hφ⟩ := exists_isFrobeniusAt_apply_primeLocalToGlobal q
  have hχφ : (χ φ : ZMod p) = ((q : ℕ) : ZMod p) :=
    coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt p q hne hφ
  have hχI : ∀ g ∈ I, χ g = 1 := fun g hg => cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia p q hne hg
  have hqk : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) q.2).1 h0).symm

  have hadm₁' : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M, H1π M c = x ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F.fixingSubgroup → c (g * s) = c g := by
    intro x
    refine (hadm₁ x).trans ⟨?_, ?_⟩
    · rintro ⟨c, hc, hx⟩; exact ⟨c, hx, hc⟩
    · rintro ⟨c, hx, hc⟩; exact ⟨c, hc, hx⟩

  have hlevel : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F → ∀ _ : Normal ℚ F,
      F₀ ≤ F →
      finrank (ZMod p) (inflationImage M ((F.fixingSubgroup).comap (primeLocalToGlobal q)))
        ≤ finrank (ZMod p) M.ρ.invariants + finrank (ZMod p) (M.dualTwist χ).ρ.invariants := by
    intro F hF hFn hF₀F
    haveI := hF; haveI := hFn
    haveI : IsGalois ℚ F := ⟨⟩
    let U : Subgroup (primeLocalGaloisGroup q) := (F.fixingSubgroup).comap r
    haveI : U.Normal := ExtCitation.levelSubgroup_normal q F
    haveI : U.FiniteIndex := ExtCitation.levelSubgroup_finiteIndex q F
    have hUM : ∀ u ∈ U, M.ρ u = 1 := fun u hu =>
      hUL u (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hF₀F)) hu)
    have hχU : ∀ u ∈ U, χ u = 1 := by
      intro u hu
      have hfix : r u (primRoot p) = primRoot p := by
        have hmem : primRoot p ∈ F :=
          (le_sup_right.trans hF₀F : K₀ ≤ F) (IntermediateField.mem_adjoin_simple_self ℚ (primRoot p))
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_comap.1 hu) _ hmem
      exact cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p (r u) (isPrimitiveRoot_primRoot p) hfix

    obtain ⟨t, W, ht, hUW, -, hWN, hWq, htame, hfrob⟩ := exists_tame_generator_at_level q φ hφ F
    haveI := hWN
    haveI : W.FiniteIndex := Subgroup.finiteIndex_of_le hUW
    haveI : Fintype (primeLocalGaloisGroup q ⧸ W) := Fintype.ofFinite _

    have hgen : ∀ g, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ I ⊔ U := fun g =>
      exists_frobenius_pow_inv_mul_mem_inertia_sup_level q φ hφ F g

    let tb : primeLocalGaloisGroup q ⧸ W := QuotientGroup.mk t
    let fb : primeLocalGaloisGroup q ⧸ W := QuotientGroup.mk φ
    have hconj : fb * tb * fb⁻¹ = tb ^ (q : ℕ) := by
      change QuotientGroup.mk φ * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹
        = (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ W) ^ (q : ℕ)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
        eq_comm, QuotientGroup.eq]
      exact hfrob
    have hst : fb * tb * fb⁻¹ ∈ Subgroup.zpowers tb :=
      ⟨(q : ℕ), by change tb ^ ((q : ℕ) : ℤ) = _; rw [zpow_natCast, hconj]⟩
    set e : ℕ := orderOf tb with he_def
    have he : 0 < e := orderOf_pos tb
    have hcop_e : Nat.Coprime (q : ℕ) e := by
      rw [Nat.Prime.coprime_iff_not_dvd q.2]
      intro hdvd
      have h1 : orderOf (tb ^ (q : ℕ)) = e := by
        rw [← hconj]
        exact (MulAut.conj fb).orderOf_eq tb
      rw [orderOf_pow' tb q.2.ne_zero, Nat.gcd_eq_right hdvd, ← he_def] at h1
      have h2 : e / (q : ℕ) < e := Nat.div_lt_self he q.2.one_lt
      omega
    have hcop_p : Nat.Coprime (q : ℕ) p :=
      (Nat.coprime_primes q.2 (Fact.out : p.Prime)).2 hne
    have hcop : Nat.Coprime (q : ℕ) (e * p) := Nat.Coprime.mul_right hcop_e hcop_p
    have hlt : 1 < e * p := by
      have := (Fact.out : p.Prime).one_lt
      nlinarith
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
    have hmod : (q : ℕ) * m ≡ 1 [MOD e * p] := by
      rw [Nat.ModEq, hm, Nat.mod_eq_of_lt hlt]
    have hmq : (m : ZMod p) * ((q : ℕ) : ZMod p) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod.of_mul_left e)
      rw [Nat.cast_mul, Nat.cast_one] at h
      rw [mul_comm]
      exact h
    have hm' : fb⁻¹ * tb * fb = tb ^ m := by
      have htqm : tb ^ ((q : ℕ) * m) = tb := by
        conv_rhs => rw [← pow_one tb]
        exact pow_eq_pow_iff_modEq.2 (hmod.of_mul_right p)
      have h1 : fb⁻¹ * tb ^ (q : ℕ) * fb = tb := by
        rw [← hconj]; group
      calc fb⁻¹ * tb * fb = fb⁻¹ * tb ^ ((q : ℕ) * m) * fb⁻¹⁻¹ := by rw [htqm, inv_inv]
        _ = (fb⁻¹ * tb ^ (q : ℕ) * fb⁻¹⁻¹) ^ m := by rw [pow_mul, conj_pow]
        _ = tb ^ m := by rw [inv_inv, h1]
    exact groupCohomology.finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist M χ U W I
      hUM hUW (q : ℕ) hqk hWq t ht htame φ hgen hχI hχU hχφ m hmq hm' hst
  exact finrank_le_of_levelBound_of_forall_iff_exists_rightInvariantRep p q M F₀ _ hlevel adm₁ hadm₁'

end S_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist
end P2MW
export P2MW.S_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist (solution)
