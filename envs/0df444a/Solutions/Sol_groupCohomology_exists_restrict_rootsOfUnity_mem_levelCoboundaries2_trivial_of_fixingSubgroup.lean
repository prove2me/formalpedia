-- Prove2me | solution 1 for groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1d8f7146-8600-5163-96f0-ca0fdf7a3d7a

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
import Theorems.Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
import Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open ExtCitation groupCohomology
open scoped IntermediateField

set_option maxHeartbeats 3200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))) [FiniteDimensional ℚ_[(q : ℕ)] K]
    (hμ : ∀ ζ : PadicAlgCl (q : ℕ), ζ ^ p = 1 → ζ ∈ K)
    (a : ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) × ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
      → Rep.trivial (ZMod p) ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p))
    (ha : a ∈ levelCocycles₂ ((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype)
      (Rep.trivial (ZMod p) ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p))) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
            × ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) =>
          a (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
        ∈ levelCoboundaries₂
            (((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype).comp
              (Subgroup.inclusion (inf_le_left : (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)) ≤ (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))))))
            (Rep.trivial (ZMod p) ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) (ZMod p)) := by
  classical
  haveI : IsGalois ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)) := IsAlgClosure.isGalois ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))
  haveI : IsGalois K (PadicAlgCl (q : ℕ)) := IsGalois.tower_top_intermediateField K

  let jK : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) →* (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)) :=
    K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom
  let rK : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal (q : ℕ)).comp jK
  have hlevelK : ∀ E : IntermediateField K (PadicAlgCl (q : ℕ)), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ, rK σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup := by
    intro E hE; haveI := hE
    exact IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le (q : ℕ) K E
  have hopenK : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl (q : ℕ)), FiniteDimensional K E ∧
        ∀ σ, σ ∈ E.fixingSubgroup → rK σ ∈ F.fixingSubgroup := by
    intro F hF; haveI := hF
    exact IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm (q : ℕ) K F

  let toS : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) →
      ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) :=
    fun σ => ⟨jK σ, ((IntermediateField.fixingSubgroupEquiv K).symm σ).2⟩

  haveI : NeZero ((p : ℕ) : PadicAlgCl (q : ℕ)) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl (q : ℕ)) p
  have hζ₀u : IsPrimitiveRoot (hζ₀.isUnit (Fact.out : p.Prime).ne_zero).unit p := IsPrimitiveRoot.isUnit_unit (Fact.out : p.Prime).ne_zero hζ₀
  let Φ : ZMod p ≃+ (Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p) :=
    hζ₀u.zmodEquivZPowers.trans (MulEquiv.subgroupCongr hζ₀u.zpowers_eq).toAdditive
  have hμfix : ∀ (σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) (x : Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p),
      (Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p).ρ σ x = x := by
    intro σ x
    apply (Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ)))).injective
    apply Subtype.ext; apply Units.ext
    show σ (((Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ))) x : rootsOfUnity p (PadicAlgCl (q : ℕ))) : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ)) = _
    obtain ⟨y, hy⟩ : ∃ y : K, (y : PadicAlgCl (q : ℕ)) = (((Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ))) x : rootsOfUnity p _) : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ)) := by
      refine ⟨⟨_, hμ _ ?_⟩, rfl⟩
      exact (mem_rootsOfUnity' p _).1 (Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ))) x).2
    rw [← hy]
    exact σ.commutes y

  let aK : ((PadicAlgCl (q : ℕ)) ≃ₐ[K] (PadicAlgCl (q : ℕ))) × ((PadicAlgCl (q : ℕ)) ≃ₐ[K] (PadicAlgCl (q : ℕ))) → Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p := fun g => Φ (a (toS g.1, toS g.2))
  have htoS_mul : ∀ σ τ : (PadicAlgCl (q : ℕ)) ≃ₐ[K] (PadicAlgCl (q : ℕ)), toS (σ * τ) = toS σ * toS τ := fun σ τ => Subtype.ext (map_mul jK σ τ)
  have haco : ∀ g h j : ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))), a (g * h, j) + a (g, h) = a (h, j) + a (g, h * j) := by
    intro g h j
    have e := (mem_cocycles₂_iff (A := Rep.trivial (ZMod p) _ (ZMod p)) a).1 ha.1 g h j
    simpa using e
  have haK : aK ∈ levelCocycles₂ rK (Kummer.kummerRep K (PadicAlgCl (q : ℕ)) p) := by
    refine (mem_levelCocycles₂_iff rK _ aK).2 ⟨?_, ?_⟩
    · rw [mem_cocycles₂_iff]
      intro σ τ υ
      simp only [aK, hμfix, htoS_mul, ← map_add, haco]
    · obtain ⟨F, hF, hlc⟩ := ha.2
      refine ⟨F, hF, fun σ σ' s s' hs hs' => ?_⟩
      simp only [aK, htoS_mul]
      rw [hlc (toS σ) (toS σ') (toS s) (toS s') hs hs']

  obtain ⟨N, hN, hmem⟩ :=
    groupCohomology.exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic (q : ℕ) p K rK hlevelK hopenK aK haK
  refine ⟨N, hN, ?_⟩

  have hfixL : ∀ g : ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
        : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))),
      IntermediateField.fixingSubgroupEquiv K ⟨g.1, g.2.1⟩ ∈ (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup := by
    intro g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    have hg : ∀ ζ : PadicAlgCl (q : ℕ), ζ ^ ((q : ℕ) ^ N - 1) = 1 →
        (IntermediateField.fixingSubgroupEquiv K ⟨g.1, g.2.1⟩) ζ = ζ := by
      intro ζ hζ
      have h2 := g.2.2
      change (show PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ) from g.1)
        ∈ (IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup at h2
      rw [IntermediateField.mem_fixingSubgroup_iff] at h2
      exact h2 ζ (IntermediateField.subset_adjoin _ _ hζ)
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap x => exact AlgEquiv.commutes _ x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]

  let m : ↥((((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) ⊓ (((IntermediateField.adjoin ℚ_[(q : ℕ)] {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
        : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q)))
      →* (PadicAlgCl (q : ℕ) ≃ₐ[(IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})] PadicAlgCl (q : ℕ)) :=
    { toFun := fun g => IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}) ⟨_, hfixL g⟩
      map_one' := by apply AlgEquiv.ext; intro x; rfl
      map_mul' := fun _ _ => by apply AlgEquiv.ext; intro x; rfl }

  have hjm : ∀ g, toS (((IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup.subtype.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm.toMonoidHom) (m g)) = Subgroup.inclusion inf_le_left g := by
    intro g
    apply Subtype.ext
    have e1 : (((IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm (m g) : (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup)
          : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ))
        = IntermediateField.fixingSubgroupEquiv K ⟨g.1, g.2.1⟩ := by
      show (((IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm
          (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}) ⟨_, hfixL g⟩) : (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup)
          : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) = _
      rw [MulEquiv.symm_apply_apply]
    show (((IntermediateField.fixingSubgroupEquiv K).symm
        (((IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm (m g) : (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup)
          : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) : K.fixingSubgroup) : PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))
      = g.1
    rw [e1, MulEquiv.symm_apply_apply]
  have hr : ∀ g, (rK.comp ((IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup.subtype.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm.toMonoidHom)) (m g)
      = (((primeLocalToGlobal q).comp (((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))).subtype).comp (Subgroup.inclusion inf_le_left)) g := by
    intro g
    exact congrArg (fun s : ↥(((K.fixingSubgroup : Subgroup (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ))) : Subgroup (primeLocalGaloisGroup q))) => primeLocalToGlobal q s.1) (hjm g)

  have hμfixL : ∀ (τ : PadicAlgCl (q : ℕ) ≃ₐ[(IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})] PadicAlgCl (q : ℕ))
      (x : Kummer.kummerRep (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}) (PadicAlgCl (q : ℕ)) p),
      (Kummer.kummerRep (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}) (PadicAlgCl (q : ℕ)) p).ρ τ x = x := by
    intro τ x
    apply (Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ)))).injective
    apply Subtype.ext; apply Units.ext
    show τ (((Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ))) x : rootsOfUnity p (PadicAlgCl (q : ℕ))) : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ)) = _
    obtain ⟨y, hy⟩ : ∃ y : K, (y : PadicAlgCl (q : ℕ)) = (((Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ))) x : rootsOfUnity p _) : (PadicAlgCl (q : ℕ))ˣ) : PadicAlgCl (q : ℕ)) := by
      refine ⟨⟨_, hμ _ ?_⟩, rfl⟩
      exact (mem_rootsOfUnity' p _).1 (Additive.toMul (α := rootsOfUnity p (PadicAlgCl (q : ℕ))) x).2
    rw [← hy]
    exact τ.commutes (algebraMap K (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}) y)

  obtain ⟨y, ⟨F, hF, hylc⟩, hyeq⟩ := (mem_levelCoboundaries₂_iff _ _ _).1 hmem
  refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨fun g => Φ.symm (y (m g)), ⟨F, hF, fun g u hu => ?_⟩, funext fun gh => ?_⟩
  · simp only
    rw [map_mul]
    exact congrArg _ (hylc (m g) (m u) (by rw [hr]; exact hu))
  · obtain ⟨g, h⟩ := gh
    rw [d₁₂_hom_apply]
    show Φ.symm (y (m h)) - Φ.symm (y (m (g * h))) + Φ.symm (y (m g)) = a (Subgroup.inclusion inf_le_left g, Subgroup.inclusion inf_le_left h)
    rw [← map_sub, ← map_add, map_mul, ← hμfixL (m g) (y (m h))]
    have e3 := congrFun hyeq (m g, m h)
    rw [d₁₂_hom_apply] at e3
    dsimp only at e3
    refine (congrArg Φ.symm e3).trans ?_
    show Φ.symm (Φ (a (toS (((IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup.subtype.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm.toMonoidHom) (m g)), toS (((IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup.subtype.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl (q : ℕ) | ζ ^ ((q : ℕ) ^ N - 1) = 1})).symm.toMonoidHom) (m h))))) = _
    rw [AddEquiv.symm_apply_apply, hjm, hjm]

end S_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup
end P2MW
export P2MW.S_groupCohomology_exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup (solution)
