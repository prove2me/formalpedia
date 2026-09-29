-- Prove2me | solution 1 for groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a1c300f6-a12f-5c13-9508-906f1a2cbed3

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen
import Theorems.Thm_groupCohomology_finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
import Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
import Theorems.Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
import Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation
open IntermediateField

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) :
    FiniteDimensional (ZMod p)
        (continuousH2 ((primeLocalToGlobal q).comp S.subtype)
          (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) ∧
      finrank (ZMod p)
        (continuousH2 ((primeLocalToGlobal q).comp S.subtype)
          (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) = 1 := by
  classical
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hp : p.Prime := Fact.out
  let Ω := PadicAlgCl (q : ℕ)
  let G := Ω ≃ₐ[ℚ_[(q : ℕ)]] Ω

  obtain ⟨KS, hKSfd, hKS⟩ := ExtCitation.exists_padicLevel_fixingSubgroup_eq_of_isOpen q S hS
  haveI := hKSfd

  let e : S ≃* (Ω ≃ₐ[KS] Ω) := (MulEquiv.subgroupCongr hKS.symm).trans (IntermediateField.fixingSubgroupEquiv KS)
  let r : (Ω ≃ₐ[KS] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal (q : ℕ)).comp
      (KS.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv KS).symm.toMonoidHom)
  have hsymm : ∀ s : S, ((IntermediateField.fixingSubgroupEquiv KS).symm (e s) : G) = (show G from (s : primeLocalGaloisGroup q)) := by
    intro s
    change (((IntermediateField.fixingSubgroupEquiv KS).symm ((IntermediateField.fixingSubgroupEquiv KS) _)) : G) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hre : ∀ s : S, r (e s) = ((primeLocalToGlobal q).comp S.subtype) s := by
    intro s
    change localGaloisToGlobal (q : ℕ) (((IntermediateField.fixingSubgroupEquiv KS).symm (e s) : G)) = _
    rw [hsymm]
    rfl

  let χ := (cycloChar p).comp (primeLocalToGlobal q)
  let χ' := (cycloChar p).comp r
  have hχ : ∀ s : S, χ' (e s) = χ (s : primeLocalGaloisGroup q) := fun s => by
    change cycloChar p (r (e s)) = cycloChar p (primeLocalToGlobal q s)
    rw [hre]
    rfl
  have hφ : ∀ (s : S) (x : Rep.res S.subtype (ofChar (k := ZMod p) χ)),
      (LinearEquiv.refl (ZMod p) (ZMod p)) ((Rep.res S.subtype (ofChar (k := ZMod p) χ)).ρ s x)
        = (ofChar (k := ZMod p) χ').ρ (e s) ((LinearEquiv.refl (ZMod p) (ZMod p)) x) := by
    intro s x
    change (χ (s : primeLocalGaloisGroup q) : ZMod p) • x = (χ' (e s) : ZMod p) • x
    rw [hχ]
  obtain ⟨-, -, ⟨Θ⟩⟩ := groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv
    ((primeLocalToGlobal q).comp S.subtype) r e hre (Rep.res S.subtype (ofChar (k := ZMod p) χ))
    (ofChar (k := ZMod p) χ') (LinearEquiv.refl (ZMod p) (ZMod p)) hφ

  have hlevel : ∀ E : IntermediateField KS Ω, FiniteDimensional KS E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[KS] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by
    intro E hE
    haveI := hE
    exact IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le (q : ℕ) KS E
  have hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField KS Ω, FiniteDimensional KS E ∧
        ∀ σ : Ω ≃ₐ[KS] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup := by
    intro F hF
    haveI := hF
    exact IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm (q : ℕ) KS F

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
  haveI : Fintype (rootsOfUnity p Ω) := Fintype.ofFinite _
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    rw [ZMod.card, ← Fintype.card_congr (Additive.ofMul (α := rootsOfUnity p Ω)), ← Nat.card_eq_fintype_card]
    exact hζΩ.card_rootsOfUnity.symm
  let eμ : (ofChar (k := ZMod p) χ') ≃+ Additive (rootsOfUnity p Ω) := AddEquiv.ofBijective f hfbij
  have heμv : ∀ m : ofChar (k := ZMod p) χ', eμ m = Additive.ofMul (ζ' ^ (show ZMod p from m).val) := fun _ => rfl
  have hsmulζ : ∀ s : S, (e s) • ζ = (show G from (s : primeLocalGaloisGroup q)) • ζ := fun _ => Units.ext rfl
  have heμ : ∀ (σ : Ω ≃ₐ[KS] Ω) (m : ofChar (k := ZMod p) χ'),
      Additive.toMul (eμ ((ofChar (k := ZMod p) χ').ρ σ m)) = σ • Additive.toMul (eμ m) := by
    intro σ m
    obtain ⟨s, rfl⟩ := e.surjective σ
    rw [heμv, heμv]
    change ζ' ^ ((χ' (e s) : ZMod p) * (show ZMod p from m)).val = (e s) • ζ' ^ (show ZMod p from m).val
    rw [hval_mul, smul_pow']
    congr 1
    apply Subtype.ext
    rw [Kummer.coe_smul_rootsOfUnity, hsmulζ, hζ, hχ]
    rfl
  obtain ⟨hfinT, hrankT⟩ := groupCohomology.finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
    (q : ℕ) KS r hlevel hopen p (ofChar (k := ZMod p) χ') eμ heμ
  haveI := hfinT
  exact ⟨Module.Finite.equiv Θ.symm, by rw [LinearEquiv.finrank_eq Θ, hrankT]⟩

end S_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen
end P2MW
export P2MW.S_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen (solution)
