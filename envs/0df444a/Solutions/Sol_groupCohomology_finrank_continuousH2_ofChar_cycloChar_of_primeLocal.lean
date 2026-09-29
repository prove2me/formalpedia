-- Prove2me | solution 1 for groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/29fb332d-9f48-5862-ac59-1c4a6c1566ea

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
import Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
import Theorems.Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
import Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_primeLocal
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation
open IntermediateField

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution {p : ℕ} [Fact p.Prime] (q : Nat.Primes) :
    FiniteDimensional (ZMod p)
        (continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) ∧
      finrank (ZMod p)
        (continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) = 1 := by
  classical
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hp : p.Prime := Fact.out

  let Ω := PadicAlgCl (q : ℕ)
  let K : IntermediateField ℚ_[(q : ℕ)] Ω := ⊥
  let e : primeLocalGaloisGroup q ≃* (Ω ≃ₐ[K] Ω) :=
    ((Subgroup.topEquiv (G := Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω)).symm.trans
      (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_bot (F := ℚ_[(q : ℕ)]) (E := Ω)).symm)).trans
      (IntermediateField.fixingSubgroupEquiv K)
  have he_apply : ∀ (g : primeLocalGaloisGroup q) (x : Ω), e g x = (show Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω from g) x :=
    fun _ _ => rfl
  let r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal (q : ℕ)).comp
      (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)
  have hsymm : ∀ g : primeLocalGaloisGroup q,
      ((IntermediateField.fixingSubgroupEquiv K).symm (e g) : Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω)
        = (show Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω from g) := by
    intro g
    change (((IntermediateField.fixingSubgroupEquiv K).symm ((IntermediateField.fixingSubgroupEquiv K) _)) : Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hre : ∀ g : primeLocalGaloisGroup q, r (e g) = primeLocalToGlobal q g := by
    intro g
    change localGaloisToGlobal (q : ℕ) (((IntermediateField.fixingSubgroupEquiv K).symm (e g) : Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω)) = _
    rw [hsymm]
    rfl

  let χ := (cycloChar p).comp (primeLocalToGlobal q)
  let χ' := (cycloChar p).comp r
  have hχ : ∀ g, χ' (e g) = χ g := fun g => by
    change cycloChar p (r (e g)) = cycloChar p (primeLocalToGlobal q g)
    rw [hre]
  have hφ : ∀ (g : primeLocalGaloisGroup q) (x : ofChar (k := ZMod p) χ),
      (LinearEquiv.refl (ZMod p) (ZMod p)) ((ofChar (k := ZMod p) χ).ρ g x)
        = (ofChar (k := ZMod p) χ').ρ (e g) ((LinearEquiv.refl (ZMod p) (ZMod p)) x) := by
    intro g x
    change (χ g : ZMod p) • x = (χ' (e g) : ZMod p) • x
    rw [hχ]
  obtain ⟨-, -, ⟨Θ⟩⟩ := groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv
    (primeLocalToGlobal q) r e hre (ofChar (k := ZMod p) χ) (ofChar (k := ZMod p) χ')
    (LinearEquiv.refl (ZMod p) (ZMod p)) hφ

  have hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by
    intro E hE
    haveI := hE
    exact IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le (q : ℕ) K E
  have hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup := by
    intro F hF
    haveI := hF
    exact IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm (q : ℕ) K F

  obtain ⟨ζ, hζp, hζ⟩ := ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal (q : ℕ) p
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ1 : ζ ^ p = 1 := hζp.pow_eq_one
  let ζ' : rootsOfUnity p Ω := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζ1⟩
  have hζ'1 : ζ' ^ p = 1 := Subtype.ext hζ1
  have hpowmod : ∀ n : ℕ, ζ' ^ (n % p) = ζ' ^ n := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hζ'1, one_pow, mul_one]
  have hval_add : ∀ a b : ZMod p, ζ' ^ (a + b).val = ζ' ^ a.val * ζ' ^ b.val := fun a b => by
    rw [ZMod.val_add, hpowmod, pow_add]
  have hval_mul : ∀ a b : ZMod p, ζ' ^ (a * b).val = (ζ' ^ a.val) ^ b.val := fun a b => by
    rw [ZMod.val_mul, hpowmod, pow_mul]
  let f : ZMod p →+ Additive (rootsOfUnity p Ω) :=
    { toFun := fun c => Additive.ofMul (ζ' ^ c.val)
      map_zero' := by rw [ZMod.val_zero, pow_zero]; rfl
      map_add' := fun a b => by rw [hval_add]; rfl }
  have hf : ∀ c : ZMod p, f c = Additive.ofMul (ζ' ^ c.val) := fun _ => rfl
  have hζΩ : IsPrimitiveRoot (ζ : Ω) p := IsPrimitiveRoot.coe_units_iff.2 hζp
  have hfinj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have h1 : ζ' ^ a.val = ζ' ^ b.val := Additive.ofMul.injective hab
    have h2 : ζ ^ a.val = ζ ^ b.val := by
      have := congrArg (fun z : rootsOfUnity p Ω => (z : Ωˣ)) h1
      simpa using this
    exact ZMod.val_injective p (hζp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h2)
  have hfbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    rw [← Nat.card_congr (Additive.ofMul (α := rootsOfUnity p Ω)), hζΩ.card_rootsOfUnity, Nat.card_eq_fintype_card,
      ZMod.card]
  let eμ : (ofChar (k := ZMod p) χ') ≃+ Additive (rootsOfUnity p Ω) := AddEquiv.ofBijective f hfbij
  have heμv : ∀ m : ofChar (k := ZMod p) χ', eμ m = Additive.ofMul (ζ' ^ (show ZMod p from m).val) := fun _ => rfl
  have hsmulζ : ∀ g : primeLocalGaloisGroup q, (e g) • ζ = (show Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω from g) • ζ :=
    fun _ => Units.ext rfl
  have heμ : ∀ (σ : Ω ≃ₐ[K] Ω) (m : ofChar (k := ZMod p) χ'),
      Additive.toMul (eμ ((ofChar (k := ZMod p) χ').ρ σ m)) = σ • Additive.toMul (eμ m) := by
    intro σ m
    obtain ⟨g, rfl⟩ := e.surjective σ
    rw [heμv, heμv]
    change ζ' ^ ((χ' (e g) : ZMod p) * (show ZMod p from m)).val = (e g) • ζ' ^ (show ZMod p from m).val
    rw [hval_mul, smul_pow']
    congr 1
    apply Subtype.ext
    rw [Kummer.coe_smul_rootsOfUnity, hsmulζ, hζ, hχ]
    rfl
  obtain ⟨hfinT, hrankT⟩ := groupCohomology.finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
    (q : ℕ) K r hlevel hopen p (ofChar (k := ZMod p) χ') eμ heμ
  haveI := hfinT
  exact ⟨Module.Finite.equiv Θ.symm, by rw [LinearEquiv.finrank_eq Θ, hrankT]⟩

end S_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_primeLocal (solution)
