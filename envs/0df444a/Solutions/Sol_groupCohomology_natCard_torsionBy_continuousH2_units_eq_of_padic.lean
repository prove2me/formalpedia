-- Prove2me | solution 1 for groupCohomology.natCard_torsionBy_continuousH2_units_eq_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9f7fa014-afdb-564e-8ff7-c21255cdf135

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Theorems.Thm_groupCohomology_exists_mem_split_adjoin_rootsOfUnity_of_padic
import Theorems.Thm_groupCohomology_exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory

namespace P2mS26S3

theorem mem_zmultiples_of_prime {B : Type*} [AddCommGroup B] {u u₀ x : B} {p : ℕ} (hp : p.Prime)
    (hx : x ∈ AddSubgroup.zmultiples u) (hu₀ : u₀ ∈ AddSubgroup.zmultiples u) (hpx : (p : ℤ) • x = 0)
    (hord : addOrderOf u₀ = p) : x ∈ AddSubgroup.zmultiples u₀ := by
  classical

  have hfin : IsOfFinAddOrder u := by
    by_contra hinf
    obtain ⟨b, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hu₀
    have hpb : ((p : ℤ) * b) • u = 0 := by
      have : (p : ℤ) • (b • u) = 0 := addOrderOf_dvd_iff_zsmul_eq_zero.1 (by rw [hord])
      rwa [smul_smul] at this
    have hb : (p : ℤ) * b = 0 := by
      by_contra hne
      exact hinf (isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨(p : ℤ) * b, hne, hpb⟩)
    have hb0 : b = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact absurd (by exact_mod_cast h) hp.ne_zero
      · exact h
    rw [hb0, zero_zsmul, addOrderOf_zero] at hord
    exact hp.one_lt.ne hord

  let Z := AddSubgroup.zmultiples u
  haveI : Finite Z := hfin.finite_zmultiples
  letI : Fintype Z := Fintype.ofFinite Z
  haveI : IsAddCyclic Z := ⟨⟨⟨u, AddSubgroup.mem_zmultiples u⟩, fun y => by
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 y.2
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, Subtype.ext hk⟩⟩⟩
  let x' : Z := ⟨x, hx⟩
  let u₀' : Z := ⟨u₀, hu₀⟩
  have hord' : addOrderOf u₀' = p :=
    ((addOrderOf_injective Z.subtype Subtype.val_injective u₀').symm).trans hord
  have hpx' : p • x' = 0 := by
    apply Subtype.ext
    show p • x = 0
    rw [← natCast_zsmul]; exact hpx

  let T : Finset Z := Finset.univ.filter fun z => p • z = 0
  have hT : T.card ≤ p := IsAddCyclic.card_nsmul_eq_zero_le hp.pos
  let M : Finset Z := (AddSubgroup.zmultiples u₀' : Set Z).toFinset
  have hMT : M ⊆ T := by
    intro z hz
    rw [Set.mem_toFinset, SetLike.mem_coe] at hz
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show p • (k • u₀') = 0
    rw [← natCast_zsmul, smul_smul, mul_comm, ← smul_smul, natCast_zsmul,
      ← hord', addOrderOf_nsmul_eq_zero, zsmul_zero]
  have hM : M.card = p := by
    rw [← hord', ← Nat.card_zmultiples u₀']
    exact (Nat.card_eq_card_toFinset _).symm
  have hTM : T = M := (Finset.eq_of_subset_of_card_le hMT (by rw [hM]; exact hT)).symm
  have hxT : x' ∈ T := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hpx'⟩
  rw [hTM] at hxT
  rw [Set.mem_toFinset, SetLike.mem_coe] at hxT
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hxT
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  exact this

end P2mS26S3

open groupCohomology IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (p : ℕ) [Fact p.Prime] :
    Nat.card (Submodule.torsionBy ℤ (continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))) (p : ℤ)) = p := by
  classical
  have hp := (Fact.out : p.Prime)

  obtain ⟨N₀, hN₀, hdeg⟩ := IntermediateField.exists_finrank_adjoin_rootsOfUnity_padic_eq q K p hp.pos
  obtain ⟨i0f, i0n⟩ := IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K N₀ hN₀
  haveI := i0f; haveI := i0n
  obtain ⟨⟨u₀, hord₀, hC₀⟩, hnest₀⟩ :=
    groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic q K r hlevel hopen N₀ hN₀
  rw [hdeg] at hord₀

  have key : ∀ x : continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)), (p : ℤ) • x = 0 →
      x ∈ AddSubgroup.zmultiples u₀ := by
    intro x hpx
    obtain ⟨N₁, hN₁, i1f, i1n, hx⟩ := groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic q K r hlevel hopen x
    haveI := i1f; haveI := i1n
    have hN : 0 < N₀ * N₁ := Nat.mul_pos hN₀ hN₁
    obtain ⟨iNf, iNn⟩ := IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K (N₀ * N₁) hN
    haveI := iNf; haveI := iNn
    obtain ⟨⟨u, -, hCN⟩, -⟩ :=
      groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic q K r hlevel hopen (N₀ * N₁) hN
    have h0N := hnest₀ (N₀ * N₁) (dvd_mul_right N₀ N₁)
    obtain ⟨-, hnest₁⟩ :=
      groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic q K r hlevel hopen N₁ hN₁
    have h1N := hnest₁ (N₀ * N₁) (dvd_mul_left N₁ N₀)
    have hxu : x ∈ AddSubgroup.zmultiples u := (Set.ext_iff.1 hCN x).1 (h1N hx)
    have hu₀u : u₀ ∈ AddSubgroup.zmultiples u :=
      (Set.ext_iff.1 hCN u₀).1 (h0N ((Set.ext_iff.1 hC₀ u₀).2 (AddSubgroup.mem_zmultiples u₀)))
    exact P2mS26S3.mem_zmultiples_of_prime hp hxu hu₀u hpx hord₀

  have hpu₀ : (p : ℤ) • u₀ = 0 := addOrderOf_dvd_iff_zsmul_eq_zero.1 (by rw [hord₀])
  have hiff : ∀ x, x ∈ Submodule.torsionBy ℤ (continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))) (p : ℤ) ↔
      x ∈ AddSubgroup.zmultiples u₀ := by
    intro x
    rw [Submodule.mem_torsionBy_iff]
    refine ⟨key x, fun hx => ?_⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
    rw [smul_smul, mul_comm, ← smul_smul, hpu₀, zsmul_zero]
  have e : Submodule.torsionBy ℤ (continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))) (p : ℤ)
      ≃ AddSubgroup.zmultiples u₀ :=
    { toFun := fun x => ⟨x.1, (hiff x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hiff x.1).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_zmultiples, hord₀]

end S_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic
end P2MW
export P2MW.S_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic (solution)
