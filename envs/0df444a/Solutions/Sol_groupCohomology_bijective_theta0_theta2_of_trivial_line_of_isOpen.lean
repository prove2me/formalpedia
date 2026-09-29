-- Prove2me | solution 1 for groupCohomology.bijective_theta0_theta2_of_trivial_line_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1276294f-0007-5efd-a66e-58156e154675

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen
import Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta0_theta2_of_trivial_line_of_isOpen
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (hχS : ∀ s : primeLocalGaloisGroup q, s ∈ S → (cycloChar p) (primeLocalToGlobal q s) = 1)
    (A : Rep (ZMod p) S) (hA : ∀ (s : S) (a : A), A.ρ s a = a) (hA1 : finrank (ZMod p) A = 1)
    (invS : continuousH2 ((primeLocalToGlobal q).comp S.subtype)
      (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] ZMod p)
    (hinvS : Function.Bijective invS)
    (θ₀ : A.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₀)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) A →ₗ[ZMod p] Module.Dual (ZMod p)
      (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype)
      (Module.Dual.eval (ZMod p) A : A →ₗ[ZMod p] A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)
        →ₗ[ZMod p] ofChar (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) invS θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₂ := by
  classical
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hp : p.Prime := Fact.out

  have hχ1 : ∀ s : S, (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) s = 1 := fun s => hχS s.1 s.2
  haveI : FiniteDimensional (ZMod p) A := Module.finite_of_finrank_pos (by rw [hA1]; exact Nat.one_pos)
  have hAρ : ∀ s : S, A.ρ s = LinearMap.id := fun s => LinearMap.ext (hA s)
  have hDρ : ∀ (s : S) (f : A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)), (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s f = f := by
    intro s f
    rw [Rep.dualTwist_ρ_apply, hχ1, hAρ, Units.val_one, one_smul, LinearMap.comp_id]
  have hNρ : ∀ (s : S) (x : ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)), (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s x = x := by
    intro s x
    change (((((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) s : (ZMod p)ˣ) : ZMod p) • (Representation.trivial (ZMod p) S (ZMod p) s) x = x
    rw [hχ1, Units.val_one, one_smul]
    rfl
  have hfdD : Module.finrank (ZMod p) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) = 1 := by
    change Module.finrank (ZMod p) (Module.Dual (ZMod p) A) = 1
    rw [Subspace.dual_finrank_eq, hA1]
  have hfdN : Module.finrank (ZMod p) (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) = 1 := Module.finrank_self (ZMod p)
  haveI : FiniteDimensional (ZMod p) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) := Module.finite_of_finrank_pos (by rw [hfdD]; exact Nat.one_pos)

  obtain ⟨hNfin, hNrank⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen (p := p) q S hS
  change FiniteDimensional (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))) at hNfin
  change Module.finrank (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))) = 1 at hNrank
  haveI := hNfin
  have hline : ∀ (L : Rep (ZMod p) S) [FiniteDimensional (ZMod p) L], Module.finrank (ZMod p) L = 1 →
      (∀ (s : S) (x : L), L.ρ s x = x) →
      FiniteDimensional (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) L) ∧ Module.finrank (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) L) = 1 := by
    intro L _ hL1 hLρ
    let ψ : L ≃ₗ[ZMod p] (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) := LinearEquiv.ofFinrankEq _ _ (by rw [hL1, hfdN])
    obtain ⟨-, -, ⟨Ψ⟩⟩ := groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv ((primeLocalToGlobal q).comp S.subtype) ((primeLocalToGlobal q).comp S.subtype)
      (MulEquiv.refl S) (fun _ => rfl) L (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) ψ
      (fun s x => by rw [hLρ, hNρ])
    exact ⟨Module.Finite.equiv Ψ.symm, by rw [LinearEquiv.finrank_eq Ψ, hNrank]⟩
  obtain ⟨hAfin, hArank⟩ := hline A hA1 hA
  obtain ⟨hDfin, hDrank⟩ := hline (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) hfdD hDρ
  haveI := hAfin
  haveI := hDfin

  have hpush : ∀ (L : Rep (ZMod p) S) (ψ : L →ₗ[ZMod p] (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)))
      (hψ : ∀ (s : S) (x : L), ψ (L.ρ s x) = (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s (ψ x))
      (hbij : Function.Bijective ψ) (z : levelCocycles₂ ((primeLocalToGlobal q).comp S.subtype) L),
      continuousH2π ((primeLocalToGlobal q).comp S.subtype) L z ≠ 0 →
      continuousH2π ((primeLocalToGlobal q).comp S.subtype) _ (levelCocycles₂Map (MonoidHom.id S) (fun _ => rfl) ψ hψ z) ≠ 0 := by
    intro L ψ hψ hbij z hz h0
    apply hz
    rw [continuousH2π_eq_zero_iff] at h0 ⊢
    let ψe := LinearEquiv.ofBijective ψ hbij
    have hψ' : ∀ (s : S) (y : ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)), ψe.symm ((ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s y) = L.ρ s (ψe.symm y) := by
      intro s y
      apply ψe.injective
      change ψ (ψe.symm _) = ψ (L.ρ s (ψe.symm y))
      rw [hψ]
      change ψe (ψe.symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      change _ = (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s (ψe (ψe.symm y))
      rw [LinearEquiv.apply_symm_apply]
    have := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := ((primeLocalToGlobal q).comp S.subtype)) (rG := ((primeLocalToGlobal q).comp S.subtype)) (MonoidHom.id S) (fun _ => rfl)
      (ψe.symm : ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p] L) hψ' h0
    have heq : cochainsPullPush₂ (MonoidHom.id S) (ψe.symm : ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p] L)
        ((levelCocycles₂Map (MonoidHom.id S) (fun _ => rfl) ψ hψ z : S × S → ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)))
        = (z : S × S → L) := by
      funext st
      obtain ⟨s, t⟩ := st
      rw [cochainsPullPush₂_apply, coe_levelCocycles₂Map, cochainsPullPush₂_apply]
      change ψe.symm (ψe (z.1 _)) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    rwa [heq] at this

  have hbij_of : ∀ {V W : Type} [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
      [FiniteDimensional (ZMod p) V] [FiniteDimensional (ZMod p) W]
      (T : V →ₗ[ZMod p] W) (v : V), T v ≠ 0 → Module.finrank (ZMod p) V = 1 → Module.finrank (ZMod p) W = 1 →
      Function.Bijective T := by
    intro V W _ _ _ _ _ _ T v hv hV hW
    have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
    have hinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).1 hV x
      rw [LinearMap.mem_ker, map_smul] at hx
      rcases smul_eq_zero.1 hx with hc | hT
      · rw [hc, zero_smul]
      · exact absurd hT hv
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hV, hW])).1 hinj⟩

  have hAinv : A.ρ.invariants = ⊤ := by
    rw [eq_top_iff]; intro a _ s; exact hA s a
  have hDinv : (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants = ⊤ := by
    rw [eq_top_iff]; intro f _ s; exact hDρ s f
  have hAinv1 : Module.finrank (ZMod p) A.ρ.invariants = 1 := by rw [hAinv, finrank_top, hA1]
  have hDinv1 : Module.finrank (ZMod p) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants = 1 := by rw [hDinv, finrank_top, hfdD]
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨a, ha⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod p) (M := A)).1 (by rw [hA1]; exact Nat.one_pos)
    let aI : A.ρ.invariants := ⟨a, fun s => hA s a⟩
    obtain ⟨c, hc⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod p)
      (M := continuousH2 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)))).1 (by rw [hDrank]; exact Nat.one_pos)
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c

    let eva : (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) :=
      (Module.Dual.eval (ZMod p) A a : Module.Dual (ZMod p) A →ₗ[ZMod p] ZMod p)
    have heva : ∀ (s : S) (f : A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)), eva ((A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s f) = (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s (eva f) := by
      intro s f; rw [hDρ, hNρ]
    have heva0 : eva ≠ 0 := by
      intro h0
      apply ha
      refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) a).1 fun f => ?_
      have := congrArg (fun T : (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p] (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) => T f) h0
      exact this
    have hevabij : Function.Bijective eva := by
      obtain ⟨f, hf⟩ : ∃ f : A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype), eva f ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact heva0 (LinearMap.ext hcon)
      exact hbij_of eva f hf hfdD hfdN
    let e := levelCocycles₂Map (MonoidHom.id S) (fun _ => rfl) eva heva z
    have hθ := hθ₀ aI z e (fun st => rfl)
    have hne : θ₀ aI (continuousH2π ((primeLocalToGlobal q).comp S.subtype) _ z) ≠ 0 := by
      rw [hθ]
      intro h0
      exact hpush _ eva heva hevabij z hc (hinvS.1 (by rw [h0, map_zero]))
    have hne' : θ₀ aI ≠ 0 := fun h => hne (by rw [h]; rfl)
    haveI : FiniteDimensional (ZMod p) (Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)))) := inferInstance
    exact hbij_of θ₀ aI hne' hAinv1 (by rw [Subspace.dual_finrank_eq, hDrank])
  ·
    obtain ⟨d, hd⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod p) (M := A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).1
      (by rw [hfdD]; exact Nat.one_pos)
    let dI : (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants := ⟨d, fun s => hDρ s d⟩
    obtain ⟨c, hc⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod p)
      (M := continuousH2 ((primeLocalToGlobal q).comp S.subtype) A)).1 (by rw [hArank]; exact Nat.one_pos)
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    let evd : A →ₗ[ZMod p] (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) := (show Module.Dual (ZMod p) A from d)
    have hevd : ∀ (s : S) (x : A), evd (A.ρ s x) = (ofChar (k := ZMod p) (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ s (evd x) := by
      intro s x; rw [hA, hNρ]
    have hevdbij : Function.Bijective evd := by
      obtain ⟨x, hx⟩ : ∃ x : A, evd x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hd (LinearMap.ext hcon)
      exact hbij_of evd x hx hA1 hfdN
    let e := levelCocycles₂Map (MonoidHom.id S) (fun _ => rfl) evd hevd z
    have hθ := hθ₂ z dI e (fun st => rfl)
    have hne : θ₂ (continuousH2π ((primeLocalToGlobal q).comp S.subtype) _ z) dI ≠ 0 := by
      rw [hθ]
      intro h0
      exact hpush _ evd hevd hevdbij z hc (hinvS.1 (by rw [h0, map_zero]))
    have hne' : θ₂ (continuousH2π ((primeLocalToGlobal q).comp S.subtype) _ z) ≠ 0 := fun h => hne (by rw [h]; rfl)
    haveI : FiniteDimensional (ZMod p) (Module.Dual (ZMod p) (A.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants) := inferInstance
    exact hbij_of θ₂ _ hne' hArank (by rw [Subspace.dual_finrank_eq, hDinv1])

end S_groupCohomology_bijective_theta0_theta2_of_trivial_line_of_isOpen
end P2MW
export P2MW.S_groupCohomology_bijective_theta0_theta2_of_trivial_line_of_isOpen (solution)
