-- Prove2me | solution 1 for groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f5519d97-0a6d-5386-9041-14ebeb7eaae6

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Theorems.Thm_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one
import Theorems.Thm_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar
import Theorems.Thm_groupCohomology_mem_coboundaries1_ofChar_iff_exists_rootOfUnity
import Theorems.Thm_IsPrimitiveRoot_existsUnique_eq_pow_val
import Theorems.Thm_groupCohomology_isLevelConstant1_primeLocalToGlobal_iff
import Theorems.Thm_Padic_natCard_units_quot_range_powMonoidHom_of_ne_two
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open groupCohomology.Kummer

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Z : Submodule (ZMod p)
      (cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal (pPrime p))))))
    (hZ : ∀ c, c ∈ Z ↔
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup (pPrime p)),
          primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
      ∀ σ ∈ ResidualGaloisRep.unitRootInertia p, c.val σ = 0) :
    FiniteDimensional (ZMod p) Z ∧ Module.finrank (ZMod p) Z ≤ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI hq : Fact (Nat.Prime (pPrime p : ℕ)) := ⟨hp⟩

  let G := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
  let χ : G →* (ZMod p)ˣ := (cycloChar p).comp (primeLocalToGlobal (pPrime p))

  obtain ⟨ζ, hζp, hζ0⟩ := ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal p p
  have hζ : ∀ g : G, g • ζ = ζ ^ (χ g : ZMod p).val := fun g => hζ0 g
  have hζL : IsPrimitiveRoot (ζ : PadicAlgCl p) p := IsPrimitiveRoot.coe_units_iff.mpr hζp
  have hinj : ∀ a b : ZMod p, ζ ^ a.val = ζ ^ b.val → a = b := fun a b h =>
    ZMod.val_injective p (hζp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  have hpowadd : ∀ a b : ZMod p, ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
    intro a b
    rw [← pow_add, pow_eq_pow_iff_modEq, ← hζp.eq_orderOf, ← ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.natCast_zmod_val, Nat.cast_add]

  have hdata : ∀ c : Z, ∃ (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ),
      algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p ∧
        ∀ σ : G, ζ ^ (c.1.val σ).val = kummerCocycle α σ := by
    intro c
    obtain ⟨hlev, -⟩ := (hZ c.1).mp c.2
    let f : G → (PadicAlgCl p)ˣ := fun g => ζ ^ (c.1.val g).val
    have hcmem : (c.1.val : G → ZMod p) ∈ cocycles₁ (ofChar χ) := c.1.2
    have hf : IsMulCocycle₁ f :=
      (isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar χ hζp hζ c.1.val).mpr hcmem
    have hfp : ∀ g, f g ^ p = 1 := fun g => by
      simp only [f]
      rw [← pow_mul, mul_comm, pow_mul, hζp.pow_eq_one, one_pow]
    have hloc := (isLevelConstant1_primeLocalToGlobal_iff (pPrime p) c.1.val).mp hlev
    change ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E ∧
        ∀ g s : G, s ∈ E.fixingSubgroup → c.1.val (g * s) = c.1.val g at hloc
    obtain ⟨K, hK, hKlev⟩ := hloc
    have hflc : ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] E ∧
        ∀ σ τ : G, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ :=
      ⟨K, hK, fun σ τ hτ => congrArg (fun n : ZMod p => ζ ^ n.val) (hKlev σ τ hτ)⟩
    obtain ⟨a, α, hα, hfκ⟩ := exists_kummerCocycle_eq_of_isMulCocycle1_of_level hf hfp hflc
    exact ⟨a, α, hα, hfκ⟩
  choose aOf αOf haOf hκOf using hdata

  have hval : ∀ c : Z, (p : ℤ) ∣ Padic.valuation (aOf c : ℚ_[p]) := by
    intro c
    by_contra hnd
    obtain ⟨-, hvan⟩ := (hZ c.1).mp c.2
    obtain ⟨τ, hτu, hτmv⟩ :=
      PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation p (aOf c : ℚ_[p]) hnd
        (αOf c : PadicAlgCl p) (haOf c).symm
    apply hτmv
    have h1 : ζ ^ (c.1.val τ).val = 1 := by rw [hvan τ hτu, ZMod.val_zero, pow_zero]
    rw [hκOf c τ, kummerCocycle_apply, div_eq_one] at h1
    have h2 := congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) h1
    exact h2

  have hvpow : ∀ (b : ℚ_[p]), b ≠ 0 → ∀ n : ℕ, Padic.valuation (b ^ n) = n * Padic.valuation b := by
    intro b hb n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Padic.valuation_mul (pow_ne_zero _ hb) hb, ih]
        push_cast
        ring

  let P : Subgroup (ℚ_[p]ˣ) := (powMonoidHom p : ℚ_[p]ˣ →* ℚ_[p]ˣ).range
  let V : ℚ_[p]ˣ →* Multiplicative (ZMod p) :=
    { toFun := fun a => Multiplicative.ofAdd (((Padic.valuation (a : ℚ_[p]) : ℤ) : ZMod p))
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← ofAdd_add, ← Int.cast_add, Units.val_mul, Padic.valuation_mul a.ne_zero b.ne_zero] }
  have hV : ∀ a : ℚ_[p]ˣ, V a = Multiplicative.ofAdd (((Padic.valuation (a : ℚ_[p]) : ℤ) : ZMod p)) :=
    fun a => rfl
  have hVP : P ≤ V.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, hV, powMonoidHom_apply, Units.val_pow_eq_pow_val, hvpow _ b.ne_zero,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, ofAdd_zero]
  let Vb : ℚ_[p]ˣ ⧸ P →* Multiplicative (ZMod p) := QuotientGroup.lift P V hVP
  have hVb_mk : ∀ a : ℚ_[p]ˣ, Vb (QuotientGroup.mk a) = V a := fun a => QuotientGroup.lift_mk P hVP a
  have hVb_surj : Function.Surjective Vb := by
    intro t
    have hpu : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp0
    refine ⟨QuotientGroup.mk ((Units.mk0 (p : ℚ_[p]) hpu) ^ (Multiplicative.toAdd t).val), ?_⟩
    rw [hVb_mk, map_pow, hV, Units.val_mk0, Padic.valuation_p, Int.cast_one, ← ofAdd_nsmul,
      nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  have hQcard : Nat.card (ℚ_[p]ˣ ⧸ P) = p ^ 2 := Padic.natCard_units_quot_range_powMonoidHom_of_ne_two hp2
  haveI : Finite (ℚ_[p]ˣ ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hQcard]; exact pow_ne_zero _ hp0)
  have hKcard : Nat.card Vb.ker = p := by
    have h1 := Vb.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hVb_surj, Subgroup.card_top, hQcard] at h1
    have h2 : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h2, pow_two] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1

  obtain ⟨σ₀', -, c₀, hσ₀c, hc₀⟩ :=
    ExtCitation.exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one p hp2
  let σ₀ : G := σ₀'
  have hχσ₀ : (χ σ₀ : ZMod p) ≠ 1 := by
    intro h1
    apply hc₀
    have hz : (ζ : PadicAlgCl p) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζp.pow_eq_one, Units.val_one]
    have e1 : σ₀ (ζ : PadicAlgCl p) = (ζ : PadicAlgCl p) ^ c₀ := hσ₀c _ hz
    have e2 : σ₀ • ζ = ζ ^ c₀ :=
      Units.ext (by rw [val_smul_units, Units.val_pow_eq_pow_val]; exact e1)
    have e3 : ζ ^ c₀ = ζ ^ (χ σ₀ : ZMod p).val := e2.symm.trans (hζ σ₀)
    rw [pow_eq_pow_iff_modEq, ← hζp.eq_orderOf] at e3
    have e4 : (c₀ : ZMod p) = (((χ σ₀ : ZMod p).val : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr e3
    rwa [ZMod.natCast_zmod_val, h1] at e4

  have hfib : ∀ c c' : Z, (aOf c)⁻¹ * aOf c' ∈ P →
      (c'.1.val : G → ZMod p) - c.1.val ∈ coboundaries₁ (ofChar χ) := by
    intro c c' hP
    obtain ⟨b, hb⟩ := hP
    rw [powMonoidHom_apply] at hb

    have hab : aOf c' = aOf c * b ^ p := by rw [hb, mul_inv_cancel_left]
    let b' : (PadicAlgCl p)ˣ := Units.map (algebraMap ℚ_[p] (PadicAlgCl p) : ℚ_[p] →* PadicAlgCl p) b
    have hb' : (b' : PadicAlgCl p) ∈ Set.range (algebraMap ℚ_[p] (PadicAlgCl p)) := ⟨b, rfl⟩

    let η : (PadicAlgCl p)ˣ := αOf c' / (αOf c * b')
    have hη : η ^ p = 1 := by
      apply Units.val_eq_one.mp
      simp only [η, div_pow, mul_pow, Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val]
      rw [← haOf c', ← haOf c, hab]
      simp only [b', Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      rw [div_self]
      exact mul_ne_zero (by rw [haOf c]; exact pow_ne_zero _ (αOf c).ne_zero)
        (pow_ne_zero _ ((map_ne_zero (algebraMap ℚ_[p] (PadicAlgCl p))).mpr b.ne_zero))
    have hdecomp : αOf c' = αOf c * b' * η := by
      simp only [η]; rw [mul_div_cancel]
    refine (mem_coboundaries1_ofChar_iff_exists_rootOfUnity χ hζp hζ _).mpr ⟨η, hη, fun g => ?_⟩

    have hκη : kummerCocycle η g = kummerCocycle (αOf c') g / kummerCocycle (αOf c) g := by
      rw [hdecomp, kummerCocycle_mul, kummerCocycle_mul]
      have : kummerCocycle b' g = 1 := by
        rw [kummerCocycle_apply, smul_units_eq_self_of_mem_range g hb', div_self']
      rw [this, mul_one, mul_div_cancel_left]
    rw [kummerCocycle_apply] at hκη
    rw [hκη, ← hκOf c g, ← hκOf c' g, Pi.sub_apply, div_eq_iff_eq_mul, ← hpowadd, sub_add_cancel]

  have hmemker : ∀ c : Z, (QuotientGroup.mk (aOf c) : ℚ_[p]ˣ ⧸ P) ∈ Vb.ker := by
    intro c
    rw [MonoidHom.mem_ker, hVb_mk, hV]
    obtain ⟨m, hm⟩ := hval c
    rw [hm, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, ofAdd_zero]
  let Ξ : Z → Vb.ker × ZMod p := fun c => (⟨QuotientGroup.mk (aOf c), hmemker c⟩, c.1.val σ₀)
  have hΞ : Function.Injective Ξ := by
    intro c c' h
    simp only [Ξ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hP' : (aOf c)⁻¹ * aOf c' ∈ P := QuotientGroup.eq.mp h1
    obtain ⟨m, hm⟩ := hfib c c' hP'

    have hmg : ∀ g : G, c'.1.val g - c.1.val g = (χ g : ZMod p) * m - m := by
      intro g
      have := congrFun hm g
      rw [d₀₁_hom_apply, Pi.sub_apply] at this
      rw [← this]
      rfl
    have hm0 : m = 0 := by
      have h := hmg σ₀
      rw [h2, sub_self, ← sub_one_mul, eq_comm, mul_eq_zero] at h
      exact h.resolve_left (sub_ne_zero.mpr hχσ₀)
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have := hmg g
    rw [hm0, mul_zero, sub_zero, sub_eq_zero] at this
    exact this.symm

  haveI : Finite (Vb.ker × ZMod p) := inferInstance
  haveI : Finite Z := Finite.of_injective Ξ hΞ
  haveI : Module.Finite (ZMod p) Z := Module.Finite.of_finite
  refine ⟨inferInstance, ?_⟩
  have hZcard : Nat.card Z = p ^ Module.finrank (ZMod p) Z := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Z), Nat.card_zmod]
  have hle : Nat.card Z ≤ Nat.card (Vb.ker × ZMod p) := Nat.card_le_card_of_injective Ξ hΞ
  rw [Nat.card_prod, hKcard, Nat.card_zmod, hZcard, ← pow_two] at hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

end S_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
end P2MW
export P2MW.S_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two (solution)
