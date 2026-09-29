-- Prove2me | solution 1 for groupCohomology.finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/790c10f7-6a5d-5866-9f9c-720a607a0348

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_euler_poincare_identity_of_hypotheses
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_and_continuousH2_of_isOpen_of_primeLocal
import Theorems.Thm_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal
import Theorems.Thm_ExtCitation_tame_or_descent_of_isSimple
import Theorems.Thm_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_isOpen
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_exists_theta1
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Theorems.Thm_Rep_dualTwist_smooth
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open CategoryTheory Module groupCohomology ExtCitation in
theorem C1_bridge {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)

    (HFIN : ∀ (S : Subgroup (primeLocalGaloisGroup q)), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) →
      ∀ (N : Rep.{0} (ZMod p) S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional (ZMod p) N →
        FiniteDimensional (ZMod p) (groupCohomology.continuousH1 ((primeLocalToGlobal q).comp S.subtype) N) ∧
          FiniteDimensional (ZMod p) (groupCohomology.continuousH2 ((primeLocalToGlobal q).comp S.subtype) N))

    (HD2 : ∀ (S : Subgroup (primeLocalGaloisGroup q)), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) →
      ∀ (B C : Rep.{0} (ZMod p) S) (ψ : B ⟶ C), (∀ n : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s n = n) → FiniteDimensional (ZMod p) B →
        Function.Surjective ψ.hom → Function.Surjective (groupCohomology.continuousH2MapHom ((primeLocalToGlobal q).comp S.subtype) ψ))

    (HTAME1 : ∀ (S : Subgroup (primeLocalGaloisGroup q)), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) →
      ∀ (N : Rep.{0} (ZMod p) S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional (ZMod p) N →
        FiniteDimensional (ZMod p) (groupCohomology.continuousH1 ((primeLocalToGlobal q).comp S.subtype) N) →
        (∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
            (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
            (S₀.subgroupOf S).Normal ∧ (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ ((cycloChar p).comp (primeLocalToGlobal q)) s = 1) ∧
            ¬ p ∣ (S₀.subgroupOf S).index) →
        Module.finrank (ZMod p) (groupCohomology.continuousH1 ((primeLocalToGlobal q).comp S.subtype) N)
          = Module.finrank (ZMod p) N.ρ.invariants + Module.finrank (ZMod p) (N.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants
            + S.index * Module.finrank (ZMod p) N)

    (HTAME2 : ∀ (S : Subgroup (primeLocalGaloisGroup q)), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) →
      ∀ (N : Rep.{0} (ZMod p) S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional (ZMod p) N →
        (∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
            (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
            (S₀.subgroupOf S).Normal ∧ (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ ((cycloChar p).comp (primeLocalToGlobal q)) s = 1) ∧
            ¬ p ∣ (S₀.subgroupOf S).index) →
        Module.finrank (ZMod p) (groupCohomology.continuousH2 ((primeLocalToGlobal q).comp S.subtype) N)
          = Module.finrank (ZMod p) (N.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)

    (HARITH : ∀ (S : Subgroup (primeLocalGaloisGroup q)), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S) →
      ∀ (N : Rep.{0} (ZMod p) S), (∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) → FiniteDimensional (ZMod p) N → Module.finrank (ZMod p) N ≠ 0 →
        (∀ W : Submodule (ZMod p) N, (∀ (s : S) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) →
        (∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
            (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
            (S₀.subgroupOf S).Normal ∧ (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ ((cycloChar p).comp (primeLocalToGlobal q)) s = 1) ∧
            ¬ p ∣ (S₀.subgroupOf S).index) ∨
        (∃ (S' : Subgroup (primeLocalGaloisGroup q)) (hle : S' ≤ S), (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S') ∧ (S'.subgroupOf S).Normal ∧ (S'.subgroupOf S).index = p ∧
            Nat.card (MonoidHom.mrange (N.ρ.comp (Subgroup.inclusion hle)))
              < Nat.card (MonoidHom.mrange N.ρ)))

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
      ∧ (H1π M).hom c = x)
    [FiniteDimensional (ZMod p) (continuousH2 (primeLocalToGlobal q) M)] :
    finrank (ZMod p) adm₁
      = finrank (ZMod p) M.ρ.invariants
        + finrank (ZMod p) (continuousH2 (primeLocalToGlobal q) M)
        + finrank (ZMod p) M := by
  classical

  let GG := primeLocalGaloisGroup q
  let r : GG →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := primeLocalToGlobal q
  have hTop : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ (⊤ : Subgroup GG) :=
    ⟨⊥, inferInstance, fun _ _ => Subgroup.mem_top _⟩
  let N : Rep (ZMod p) (⊤ : Subgroup GG) := Rep.res (⊤ : Subgroup GG).subtype M
  haveI : FiniteDimensional (ZMod p) N := ‹FiniteDimensional (ZMod p) M›
  have hsmN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : (⊤ : Subgroup GG), ((primeLocalToGlobal q).comp (⊤ : Subgroup GG).subtype) s ∈ F.fixingSubgroup →
        N.ρ s n = n :=
    fun n => (hsm n).imp fun F h => ⟨h.1, fun s hs => h.2 s hs⟩
  have E := groupCohomology.euler_poincare_identity_of_hypotheses p (primeLocalToGlobal q)
    ((cycloChar p).comp (primeLocalToGlobal q))
    (fun (S : Subgroup (primeLocalGaloisGroup q)) (N : Rep.{0} (ZMod p) S) =>
      ∃ S₀ : Subgroup (primeLocalGaloisGroup q), S₀ ≤ S ∧
        (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S₀) ∧
        (S₀.subgroupOf S).Normal ∧ (∀ s : S, (s : primeLocalGaloisGroup q) ∈ S₀ → N.ρ s = 1 ∧ ((cycloChar p).comp (primeLocalToGlobal q)) s = 1) ∧
        ¬ p ∣ (S₀.subgroupOf S).index)
    HFIN HD2 HTAME1 HTAME2 HARITH ⊤ hTop N hsmN
  rw [Subgroup.index_top, one_mul] at E

  have hadm : adm₁ = continuousH1 (primeLocalToGlobal q) M :=
    eq_continuousH1_of_forall_mem_iff (primeLocalToGlobal q) M adm₁ hadm₁

  let e : (⊤ : Subgroup GG) ≃* GG := Subgroup.topEquiv
  let r₁ : (⊤ : Subgroup GG) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (primeLocalToGlobal q).comp (⊤ : Subgroup GG).subtype
  have he : ∀ x : (⊤ : Subgroup GG), r (e x) = r₁ x := fun _ => rfl
  have he' : ∀ g : GG, r₁ (e.symm g) = r g := fun _ => rfl
  have t0 : finrank (ZMod p) N.ρ.invariants = finrank (ZMod p) M.ρ.invariants := by
    have : ∀ v : M, v ∈ N.ρ.invariants ↔ v ∈ M.ρ.invariants := fun v =>
      ⟨fun h g => h (e.symm g), fun h x => h (e x)⟩
    exact (LinearEquiv.ofLinear
      ((N.ρ.invariants.subtype).codRestrict M.ρ.invariants fun v => (this v).1 v.2)
      ((M.ρ.invariants.subtype).codRestrict N.ρ.invariants fun v => (this v).2 v.2)
      (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)).finrank_eq
  have t1 : finrank (ZMod p) (continuousH1 r₁ N) = finrank (ZMod p) (continuousH1 r M) := by
    let φ : Rep.res e.toMonoidHom M ⟶ N :=
      Rep.ofHom ((LinearMap.id : M →ₗ[ZMod p] M).intertwiningMap_of_isIntertwiningMap
        (Rep.res e.toMonoidHom M).ρ N.ρ (fun _ _ => rfl))
    let ψ : Rep.res e.symm.toMonoidHom N ⟶ M :=
      Rep.ofHom ((LinearMap.id : M →ₗ[ZMod p] M).intertwiningMap_of_isIntertwiningMap
        (Rep.res e.symm.toMonoidHom N).ρ M.ρ (fun _ _ => rfl))
    have cφ : ∀ c : cocycles₁ M, (mapCocycles₁ e.toMonoidHom φ c : (⊤ : Subgroup GG) → M) = fun g => c (e g) :=
      fun _ => rfl
    have cψ : ∀ c : cocycles₁ N, (mapCocycles₁ e.symm.toMonoidHom ψ c : GG → M) = fun y => c (e.symm y) :=
      fun _ => rfl
    have Hφ : ∀ c : cocycles₁ M, (map e.toMonoidHom φ 1).hom ((H1π M).hom c)
        = (H1π N).hom (mapCocycles₁ e.toMonoidHom φ c) := fun c => H1π_comp_map_apply _ _ c
    have Hψ : ∀ c : cocycles₁ N, (map e.symm.toMonoidHom ψ 1).hom ((H1π N).hom c)
        = (H1π M).hom (mapCocycles₁ e.symm.toMonoidHom ψ c) := fun c => H1π_comp_map_apply _ _ c
    have mφ : ∀ x : continuousH1 r M, (map e.toMonoidHom φ 1).hom (x : H1 M) ∈ continuousH1 r₁ N := by
      intro x
      obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff r M _).1 x.2
      rw [← hx, Hφ]
      exact H1π_mem_continuousH1 r₁ N ⟨F, hF, fun g s hs => by
        rw [cφ]; show c (e (g * s)) = c (e g); rw [map_mul]; exact hc (e g) (e s) hs⟩
    have mψ : ∀ x : continuousH1 r₁ N, (map e.symm.toMonoidHom ψ 1).hom (x : H1 N) ∈ continuousH1 r M := by
      intro x
      obtain ⟨c, ⟨F, hF, hc⟩, hx⟩ := (mem_continuousH1_iff r₁ N _).1 x.2
      rw [← hx, Hψ]
      exact H1π_mem_continuousH1 r M ⟨F, hF, fun g s hs => by
        rw [cψ]; show c (e.symm (g * s)) = c (e.symm g); rw [map_mul]; exact hc (e.symm g) (e.symm s) hs⟩
    let Φ : continuousH1 r M →ₗ[ZMod p] continuousH1 r₁ N :=
      ((map e.toMonoidHom φ 1).hom ∘ₗ (continuousH1 r M).subtype).codRestrict _ mφ
    let Ψ : continuousH1 r₁ N →ₗ[ZMod p] continuousH1 r M :=
      ((map e.symm.toMonoidHom ψ 1).hom ∘ₗ (continuousH1 r₁ N).subtype).codRestrict _ mψ
    have h1 : ∀ x, Φ (Ψ x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff r₁ N _).1 x.2
      apply Subtype.ext
      show (map e.toMonoidHom φ 1).hom ((map e.symm.toMonoidHom ψ 1).hom (x : H1 N)) = x
      rw [← hx, Hψ, Hφ]
      congr 1
      all_goals
        apply cocycles₁_ext
        intro g
        exact ((congrFun (cφ _) g).trans (congrFun (cψ c) (e g))).trans (congrArg c (e.symm_apply_apply g))
    have h2 : ∀ x, Ψ (Φ x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff r M _).1 x.2
      apply Subtype.ext
      show (map e.symm.toMonoidHom ψ 1).hom ((map e.toMonoidHom φ 1).hom (x : H1 M)) = x
      rw [← hx, Hφ, Hψ]
      congr 1
      all_goals
        apply cocycles₁_ext
        intro y
        exact ((congrFun (cψ _) y).trans (congrFun (cφ c) (e.symm y))).trans (congrArg c (e.apply_symm_apply y))
    exact (LinearEquiv.ofLinear Ψ Φ (LinearMap.ext h2) (LinearMap.ext h1)).finrank_eq
  have t2 : finrank (ZMod p) (continuousH2 r₁ N) = finrank (ZMod p) (continuousH2 r M) := by
    let Φ : continuousH2 r M →ₗ[ZMod p] continuousH2 r₁ N :=
      continuousH2Map e.toMonoidHom he (LinearMap.id : M →ₗ[ZMod p] M) (fun _ _ => rfl)
    let Ψ : continuousH2 r₁ N →ₗ[ZMod p] continuousH2 r M :=
      continuousH2Map e.symm.toMonoidHom he' (LinearMap.id : M →ₗ[ZMod p] M) (fun _ _ => rfl)
    have h1 : ∀ z, Φ (Ψ z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π r₁ N _ = continuousH2π r₁ N x
      congr 1
      all_goals
        apply Subtype.ext
        funext pq
        change (x : (⊤ : Subgroup GG) × (⊤ : Subgroup GG) → M) (e.symm (e pq.1), e.symm (e pq.2)) = (x : _ → M) pq
        simp only [MulEquiv.symm_apply_apply, Prod.mk.eta]
    have h2 : ∀ z, Ψ (Φ z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π r M _ = continuousH2π r M x
      congr 1
      all_goals
        apply Subtype.ext
        funext pq
        change (x : GG × GG → M) (e (e.symm pq.1), e (e.symm pq.2)) = (x : GG × GG → M) pq
        simp only [MulEquiv.apply_symm_apply, Prod.mk.eta]
    exact (LinearEquiv.ofLinear Ψ Φ (LinearMap.ext h2) (LinearMap.ext h1)).finrank_eq
  have tN : finrank (ZMod p) N = finrank (ZMod p) M := rfl
  rw [hadm, ← t1, E, t0, t2, tN]

open CategoryTheory Module groupCohomology ExtCitation in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hq : (q : ℕ) = p)
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
      ∧ (H1π M).hom c = x)
    [FiniteDimensional (ZMod p) (continuousH2 (primeLocalToGlobal q) M)] :
    finrank (ZMod p) adm₁
      = finrank (ZMod p) M.ρ.invariants
        + finrank (ZMod p) (continuousH2 (primeLocalToGlobal q) M)
        + finrank (ZMod p) M := by
  refine C1_bridge q hq ?_ ?_ ?_ ?_ ?_ M hsm adm₁ hadm₁
  ·
    exact groupCohomology.finiteDimensional_continuousH1_and_continuousH2_of_isOpen_of_primeLocal q
  ·
    intro S hS B C ψ hsmB hfdB hψ
    haveI := hfdB
    exact groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal q S hS ψ hsmB hψ
  ·
    intro S hS N hsmN hfdN _ htame
    haveI := hfdN
    exact groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_index_mul_of_tame q hq S N htame
  ·
    intro S hS N hsmN hfdN _
    haveI := hfdN
    obtain ⟨hfd2, h1⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen (p := p) q S hS
    haveI := hfd2
    let inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
        (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) ≃ₗ[ZMod p] ZMod p :=
      LinearEquiv.ofFinrankEq _ _ (by rw [h1, Module.finrank_self])
    have hφ := Rep.isEquivariantBilinear_eval_dualTwist N (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
    obtain ⟨⟨θ₀, hθ₀⟩, ⟨θ₂, hθ₂⟩⟩ :=
      groupCohomology.exists_theta0_and_theta2 ((primeLocalToGlobal q).comp S.subtype) _ hφ inv.toLinearMap
    obtain ⟨Fχ, hFχ, hχ1⟩ :=
      groupCohomology.exists_level_ofChar_cycloChar_comp (p := p) ((primeLocalToGlobal q).comp S.subtype) (1 : ZMod p)
    have hsmD := Rep.dualTwist_smooth ((primeLocalToGlobal q).comp S.subtype) N
      (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) hsmN
      ⟨Fχ, hFχ, fun s hs => by
        have h : ((((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype s : (ZMod p)ˣ) : ZMod p) * 1 = 1 := hχ1 s hs
        rw [mul_one] at h
        exact Units.val_eq_one.mp h⟩
    obtain ⟨θ₁, hθ₁⟩ := groupCohomology.exists_theta1 ((primeLocalToGlobal q).comp S.subtype) _ hφ hsmD inv.toLinearMap
    obtain ⟨-, -, hb₂⟩ := groupCohomology.bijective_theta_dualTwist_of_isOpen q S hS N hsmN inv.toLinearMap inv.bijective
      θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂
    exact (LinearEquiv.ofBijective θ₂ hb₂).finrank_eq.trans Subspace.dual_finrank_eq
  ·
    intro S hS N hsmN hfdN hN hsimple
    haveI := hfdN
    exact ExtCitation.tame_or_descent_of_isSimple q hq S hS N hsmN hN hsimple

end S_groupCohomology_finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal (solution)
