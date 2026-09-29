-- Prove2me | solution 1 for groupCohomology.finrank_cocycles_level_le_two_of_finrank_eq_one_of_not_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d696aafc-acb4-5d1b-93c0-6e2f7e677965

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH2_of_primeLocal
import Theorems.Thm_groupCohomology_finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal
import Theorems.Thm_ExtCitation_exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Theorems.Thm_groupCohomology_finiteDimensional_continuousH1_of_isOpen_of_primeLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_cocycles_level_le_two_of_finrank_eq_one_of_not_cyclotomic
p2m_attr_erase "instance" "groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.cup_apply groupCohomology.cupCochain_apply groupCohomology.H1desc_H1π groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO IsLocalRing.principalUnits_zero groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

namespace S17K3

theorem finiteDimensional_continuousH1_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep.{0} (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) :
    FiniteDimensional (ZMod p) (continuousH1 (primeLocalToGlobal q) M) := by
  classical
  let S : Subgroup (primeLocalGaloisGroup q) := ⊤
  let N : Rep (ZMod p) ↥S := Rep.res S.subtype M
  let rS := (primeLocalToGlobal q).comp S.subtype
  haveI : FiniteDimensional (ZMod p) N := inferInstanceAs (FiniteDimensional (ZMod p) M)
  have hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S := ⟨⊥, inferInstance, le_top⟩
  have hsmN : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : ↥S, rS s ∈ F.fixingSubgroup → N.ρ s n = n := by
    intro n
    obtain ⟨F, hF, h⟩ := hsm n
    exact ⟨F, hF, fun s hs => h s.1 hs⟩
  haveI hfin : FiniteDimensional (ZMod p) (continuousH1 rS N) :=
    groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal q S hS N hsmN

  let V : Submodule (ZMod p) (cocycles₁ N) := levelCocycles₁ rS N
  let φ : V →ₗ[ZMod p] H1 N := (H1π N).hom ∘ₗ V.subtype
  have hrange : LinearMap.range φ = continuousH1 rS N := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  haveI : FiniteDimensional (ZMod p) (LinearMap.range φ) := by rw [hrange]; infer_instance
  have hker : ∀ c : V, c ∈ LinearMap.ker φ → ((c : cocycles₁ N) : ↥S → N) ∈ coboundaries₁ N := by
    intro c hc
    rw [LinearMap.mem_ker] at hc
    exact (H1π_eq_zero_iff (c : cocycles₁ N)).mp hc
  haveI : FiniteDimensional (ZMod p) (coboundaries₁ N) := by
    unfold coboundaries₁
    infer_instance
  let ψ : LinearMap.ker φ →ₗ[ZMod p] coboundaries₁ N :=
    { toFun := fun c => ⟨((c.1 : cocycles₁ N) : ↥S → N), hker c.1 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := by
    intro c c' h
    have h1 := congrArg Subtype.val h
    have h2 : (c.1 : cocycles₁ N) = (c'.1 : cocycles₁ N) := DFunLike.coe_injective h1
    exact Subtype.ext (Subtype.ext h2)
  haveI : FiniteDimensional (ZMod p) (LinearMap.ker φ) := Module.Finite.of_injective ψ hψ
  haveI : FiniteDimensional (ZMod p) (V ⧸ LinearMap.ker φ) :=
    Module.Finite.equiv (φ.quotKerEquivRange).symm
  haveI hV : FiniteDimensional (ZMod p) V := Module.Finite.of_submodule_quotient (LinearMap.ker φ)

  have hcoc : ∀ c : V, (fun g : primeLocalGaloisGroup q => ((c : cocycles₁ N) : ↥S → N) ⟨g, trivial⟩) ∈
      cocycles₁ M := by
    intro c
    rw [mem_cocycles₁_iff]
    intro g h
    have := (mem_cocycles₁_iff ((c : cocycles₁ N) : ↥S → N)).mp (c : cocycles₁ N).2 ⟨g, trivial⟩ ⟨h, trivial⟩
    exact this
  have hlev : ∀ c : V, IsLevelConstant₁ (primeLocalToGlobal q)
      (fun g : primeLocalGaloisGroup q => ((c : cocycles₁ N) : ↥S → N) ⟨g, trivial⟩) := by
    intro c
    obtain ⟨F, hF, h⟩ := (mem_levelCocycles₁_iff rS N (c : cocycles₁ N)).mp c.2
    exact ⟨F, hF, fun g s hs => h ⟨g, trivial⟩ ⟨s, trivial⟩ hs⟩
  let Ξ : V →ₗ[ZMod p] levelCocycles₁ (primeLocalToGlobal q) M :=
    { toFun := fun c => ⟨⟨_, hcoc c⟩, hlev c⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΞ : Function.Surjective Ξ := by
    intro c'
    have hc'coc : (fun s : ↥S => ((c' : cocycles₁ M) : primeLocalGaloisGroup q → M) s.1) ∈ cocycles₁ N := by
      rw [mem_cocycles₁_iff]
      intro s t
      exact (mem_cocycles₁_iff _).mp (c' : cocycles₁ M).2 s.1 t.1
    have hc'lev : (⟨_, hc'coc⟩ : cocycles₁ N) ∈ V := by
      obtain ⟨F, hF, h⟩ := (mem_levelCocycles₁_iff (primeLocalToGlobal q) M (c' : cocycles₁ M)).mp c'.2
      exact ⟨F, hF, fun g s hs => h g.1 s.1 hs⟩
    refine ⟨⟨⟨_, hc'coc⟩, hc'lev⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  haveI : FiniteDimensional (ZMod p) (levelCocycles₁ (primeLocalToGlobal q) M) :=
    Module.Finite.of_surjective Ξ hΞ
  show FiniteDimensional (ZMod p) ((levelCocycles₁ (primeLocalToGlobal q) M).map (H1π M).hom)
  infer_instance

theorem invariants_dualTwist_eq_bot_of_finrank_eq_one
    {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    {G : Type} [Group G] (χ : G →* (ZMod p)ˣ)
    (M : Rep.{0} (ZMod p) G) [Module k M] [IsScalarTower (ZMod p) k M]
    (hM : Module.finrank k M = 1)
    (hlin : ∀ (g : G) (a : k) (m : M), M.ρ g (a • m) = a • M.ρ g m)
    (hne : ∃ (g : G) (m : M), M.ρ g m ≠ algebraMap (ZMod p) k (χ g : ZMod p) • m) :
    (M.dualTwist χ).ρ.invariants = ⊥ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set ι : ZMod p →+* k := algebraMap (ZMod p) k with hι

  haveI : Module.Finite k M := Module.finite_of_finrank_eq_succ hM
  let b := Module.finBasisOfFinrankEq k M hM
  set m₀ : M := b 0 with hm₀
  have hrepr : ∀ m : M, m = (b.repr m 0) • m₀ := by
    intro m
    conv_lhs => rw [← b.sum_repr m]
    rw [Fin.sum_univ_one]

  obtain ⟨g, m₁, hgm₁⟩ := hne
  set ψ : k := b.repr (M.ρ g m₀) 0 with hψ
  have hgm₀ : M.ρ g m₀ = ψ • m₀ := hrepr _
  have hg_smul : ∀ a : k, M.ρ g (a • m₀) = (a * ψ) • m₀ := by
    intro a; rw [hlin, hgm₀, smul_smul]
  have hψne : ψ ≠ ι (χ g : ZMod p) := by
    intro heq
    apply hgm₁
    rw [hrepr m₁, hg_smul, heq, mul_comm, ← smul_smul]

  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [Representation.mem_invariants] at hf
  by_contra hf0

  have hstar : ∀ m : M, f (M.ρ g m) = (χ g : ZMod p) * f m := by
    intro m
    have h := LinearMap.congr_fun (hf g) (M.ρ g m)
    rw [Rep.dualTwist_ρ_apply, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, smul_eq_mul] at h
    exact h.symm

  let lam : k →ₗ[ZMod p] ZMod p := f ∘ₗ ((LinearMap.toSpanSingleton k M m₀).restrictScalars (ZMod p))
  have hlam : ∀ a : k, lam a = f (a • m₀) := fun a => rfl
  have hlamψ : ∀ a : k, lam (ψ * a) = (χ g : ZMod p) * lam a := by
    intro a
    rw [hlam, hlam, mul_comm, ← hg_smul, hstar]
  have hlam0 : ∃ a : k, lam a ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf0
    apply LinearMap.ext
    intro m
    rw [hrepr m, LinearMap.zero_apply, ← hlam]
    exact hall _

  have hlamψn : ∀ (n : ℕ) (a : k), lam (ψ ^ n * a) = (χ g : ZMod p) ^ n * lam a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih => intro a; rw [pow_succ, mul_assoc, ih, hlamψ, pow_succ]; ring
  have hβ : ∀ a : k, lam ((ψ ^ p - ψ) * a) = 0 := by
    intro a
    have e1 := hlamψn p a
    have e2 := hlamψn 1 a
    rw [pow_one, pow_one] at e2
    rw [sub_mul, map_sub, e1, e2, ZMod.pow_card, sub_self]
  have hβ0 : ψ ^ p - ψ = 0 := by
    by_contra hne0
    obtain ⟨a, ha⟩ := hlam0
    apply ha
    have := hβ ((ψ ^ p - ψ)⁻¹ * a)
    rwa [← mul_assoc, mul_inv_cancel₀ hne0, one_mul] at this

  have hroot : ∃ t₀ : ZMod p, ι t₀ = ψ := by
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    set P : Polynomial k := Polynomial.X ^ p - Polynomial.X with hP
    have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
    have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq k hp1
    have hmemroots : ∀ x : k, x ∈ P.roots.toFinset ↔ x ^ p - x = 0 := by
      intro x
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    let S : Finset k := Finset.univ.image ι
    have hScard : S.card = p := by
      rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, ZMod.card]
    have hSroots : S ⊆ P.roots.toFinset := by
      intro x hx
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hmemroots, ← map_pow, ZMod.pow_card, sub_self]
    have hcard_le : P.roots.toFinset.card ≤ S.card := by
      rw [hScard]
      calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ = p := hdeg
    have hEq : S = P.roots.toFinset := Finset.eq_of_subset_of_card_le hSroots hcard_le
    have hψroot : ψ ∈ P.roots.toFinset := (hmemroots ψ).mpr hβ0
    rw [← hEq] at hψroot
    obtain ⟨t₀, -, ht₀⟩ := Finset.mem_image.mp hψroot
    exact ⟨t₀, ht₀⟩
  obtain ⟨t₀, ht₀⟩ := hroot

  obtain ⟨a, ha⟩ := hlam0
  have h1 : lam (ψ * a) = t₀ * lam a := by
    rw [← ht₀, hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : t₀ = (χ g : ZMod p) := by
    have := h1.symm.trans (hlamψ a)
    exact mul_right_cancel₀ ha this
  exact hψne (by rw [← ht₀, h2])

theorem natCast_eq_cycloChar_of_forall_pow_eq
    (p : ℕ) [Fact p.Prime] (g : primeLocalGaloisGroup (pPrime p)) (c : ℕ)
    (hc : ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p g ζ = ζ ^ c) :
    (c : ZMod p) = ((cycloChar p).comp (primeLocalToGlobal (pPrime p)) g : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ, hgal⟩ :=
    ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal p p
  have hpp : (0 : ℕ) < p := (Fact.out : p.Prime).pos

  have hζL : IsPrimitiveRoot (ζ : PadicAlgCl p) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have h1 : ResidualGaloisRep.localAut p g (ζ : PadicAlgCl p) = (ζ : PadicAlgCl p) ^ c :=
    hc _ (by rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])
  have h2 : ResidualGaloisRep.localAut p g (ζ : PadicAlgCl p) =
      (ζ : PadicAlgCl p) ^ (cycloChar p (localGaloisToGlobal p (ResidualGaloisRep.localAut p g)) : ZMod p).val := by
    have := congrArg Units.val (hgal (ResidualGaloisRep.localAut p g))
    rw [Units.val_pow_eq_pow_val] at this
    rw [← this]
    rfl
  have h3 : (ζ : PadicAlgCl p) ^ c =
      (ζ : PadicAlgCl p) ^ (cycloChar p (localGaloisToGlobal p (ResidualGaloisRep.localAut p g)) : ZMod p).val := by
    rw [← h1, h2]
  set v : ℕ := ((cycloChar p (localGaloisToGlobal p (ResidualGaloisRep.localAut p g)) : ZMod p)).val with hv
  have hvlt : v < p := ZMod.val_lt _
  rw [pow_eq_pow_mod c hζL.pow_eq_one, pow_eq_pow_mod v hζL.pow_eq_one] at h3
  have hmod : c % p = v % p := hζL.pow_inj (Nat.mod_lt _ hpp) (Nat.mod_lt _ hpp) h3
  rw [Nat.mod_eq_of_lt hvlt] at hmod
  have h4 : (c : ZMod p) = ((c % p : ℕ) : ZMod p) := (ZMod.natCast_mod c p).symm
  rw [h4, hmod, hv, ZMod.natCast_zmod_val]
  rfl

section Line

variable {k : Type} [Field k] {G : Type} [Group G]

lemma apply_eq_det_smul {V : Type*} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 1)
    (f : Module.End k V) (v : V) : f v = LinearMap.det f • v := by
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  let b := Module.finBasisOfFinrankEq k V hV
  have hrepr : ∀ w : V, w = b.repr w 0 • b 0 := fun w => by
    conv_lhs => rw [← b.sum_repr w]
    rw [Fin.sum_univ_one]
  have hf : f = (b.repr (f (b 0)) 0) • (LinearMap.id : Module.End k V) := by
    refine b.ext fun i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact hrepr (f (b 0))
  have hdet : LinearMap.det f = b.repr (f (b 0)) 0 := by
    conv_lhs => rw [hf]
    rw [LinearMap.det_smul, LinearMap.det_id, hV, pow_one, mul_one]
  rw [hdet]
  conv_lhs => rw [hf]
  rw [LinearMap.smul_apply, LinearMap.id_apply]

variable (N : Rep k G)

noncomputable def lineChar : G →* kˣ :=
  ((LinearMap.det : Module.End k N →* k).comp N.ρ).toHomUnits

lemma lineChar_apply (g : G) : (lineChar N g : k) = LinearMap.det (N.ρ g) := rfl

variable {N} in
lemma ρ_apply_eq_lineChar_smul (hN : Module.finrank k N = 1) (g : G) (m : N) :
    N.ρ g m = (lineChar N g : k) • m := by
  rw [lineChar_apply]; exact apply_eq_det_smul hN _ _

lemma ofChar_ρ_apply (ψ : G →* kˣ) (g : G) (a : k) : (ofChar ψ).ρ g a = (ψ g : k) * a := rfl

variable {N} in

noncomputable def cocyclesLineEquiv (φ : N ≃ₗ[k] k) (ψ : G →* kˣ)
    (hρ : ∀ (g : G) (m : N), N.ρ g m = (ψ g : k) • m) :
    cocycles₁ N ≃ₗ[k] cocycles₁ (ofChar ψ) where
  toFun c := ⟨fun g => φ (c g), by
    rw [mem_cocycles₁_iff]
    intro g h
    have hc := (mem_cocycles₁_iff (c : G → N)).1 c.2 g h
    change φ (c (g * h)) = (ψ g : k) * φ (c h) + φ (c g)
    rw [hc, map_add, hρ, map_smul, smul_eq_mul]⟩
  invFun f := ⟨fun g => φ.symm (f g), by
    rw [mem_cocycles₁_iff]
    intro g h
    have hf := (mem_cocycles₁_iff (f : G → k)).1 f.2 g h
    change φ.symm (f (g * h)) = N.ρ g (φ.symm (f h)) + φ.symm (f g)
    rw [hf, map_add, hρ, ← map_smul]
    rfl⟩
  map_add' c c' := by
    apply cocycles₁_ext
    intro g
    exact map_add φ (c g) (c' g)
  map_smul' a c := by
    apply cocycles₁_ext
    intro g
    exact map_smul φ a (c g)
  left_inv c := by
    apply cocycles₁_ext
    intro g
    exact φ.symm_apply_apply (c g)
  right_inv f := by
    apply cocycles₁_ext
    intro g
    exact φ.apply_symm_apply (f g)

variable {N} in
lemma cocyclesLineEquiv_apply (φ : N ≃ₗ[k] k) (ψ : G →* kˣ)
    (hρ : ∀ (g : G) (m : N), N.ρ g m = (ψ g : k) • m) (c : cocycles₁ N) (g : G) :
    cocyclesLineEquiv φ ψ hρ c g = φ (c g) := rfl

variable {N} in
lemma cocyclesLineEquiv_symm_apply (φ : N ≃ₗ[k] k) (ψ : G →* kˣ)
    (hρ : ∀ (g : G) (m : N), N.ρ g m = (ψ g : k) • m) (f : cocycles₁ (ofChar ψ)) (g : G) :
    (cocyclesLineEquiv φ ψ hρ).symm f g = φ.symm (f g) := rfl

end Line

section Restrict

variable {R k : Type} [CommRing R] [CommRing k] {G : Type} [Group G]
variable (N : Rep.{0} k G) [Module R N] [SMul R k] [IsScalarTower R k N]

def resρ : Representation R G N where
  toFun g := (N.ρ g).restrictScalars R
  map_one' := by ext m; simp
  map_mul' g h := by ext m; simp

abbrev resRep : Rep.{0} R G := Rep.of (resρ (R := R) N)

lemma resRep_ρ_apply (g : G) (m : N) : (resRep (R := R) N).ρ g m = N.ρ g m := rfl

lemma mem_cocycles₁_resRep_iff (f : G → N) :
    f ∈ cocycles₁ (resRep (R := R) N) ↔ f ∈ cocycles₁ N := by
  rw [mem_cocycles₁_iff, mem_cocycles₁_iff]
  rfl

def cocyclesResEquiv : cocycles₁ N ≃ₗ[R] cocycles₁ (resRep (R := R) N) where
  toFun c := ⟨c.1, (mem_cocycles₁_resRep_iff N c.1).2 c.2⟩
  invFun c := ⟨c.1, (mem_cocycles₁_resRep_iff N c.1).1 c.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Restrict

section Count

variable {p : ℕ} [Fact p.Prime]

local notation "Gp" => primeLocalGaloisGroup (pPrime p)
local notation "loc" => primeLocalToGlobal (pPrime p)

lemma comap_coboundaries₁_le_levelCocycles₁ (M : Rep.{0} (ZMod p) Gp)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, (loc) s ∈ F.fixingSubgroup → M.ρ s m = m) :
    (coboundaries₁ M).comap (cocycles₁ M).subtype ≤ levelCocycles₁ (loc) M := by
  intro c hc
  obtain ⟨m, hm⟩ := (Submodule.mem_comap.1 hc : (c : Gp → M) ∈ coboundaries₁ M)
  rw [mem_levelCocycles₁_iff]
  obtain ⟨F, hF, hFm⟩ := hsm m
  refine ⟨F, hF, fun g s hs => ?_⟩
  have hc' : ∀ x, c x = M.ρ x m - m := fun x => by
    change ((cocycles₁ M).subtype c) x = _
    rw [← hm, d₀₁_hom_apply]
  rw [hc', hc', map_mul, Module.End.mul_apply, hFm s hs]

lemma ker_H1π_eq (M : Rep.{0} (ZMod p) Gp) :
    LinearMap.ker (H1π M).hom = (coboundaries₁ M).comap (cocycles₁ M).subtype := by
  ext c
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  exact H1π_eq_zero_iff c

theorem finrank_levelCocycles₁_eq (M : Rep.{0} (ZMod p) Gp) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, (loc) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (h0 : M.ρ.invariants = ⊥)
    (h2 : (M.dualTwist ((cycloChar p).comp (loc))).ρ.invariants = ⊥) :
    FiniteDimensional (ZMod p) (levelCocycles₁ (loc) M) ∧
      Module.finrank (ZMod p) (levelCocycles₁ (loc) M) = 2 * Module.finrank (ZMod p) M := by
  classical
  haveI hH1 : FiniteDimensional (ZMod p) (continuousH1 (loc) M) :=
    finiteDimensional_continuousH1_of_primeLocal (pPrime p) M hsm
  haveI hH2 : FiniteDimensional (ZMod p) (continuousH2 (loc) M) :=
    finiteDimensional_continuousH2_of_primeLocal (p := p) (pPrime p) rfl M hsm
  have hEuler := finrank_continuousClasses_eq_invariants_add_continuousH2_add_finrank_of_primeLocal
    (p := p) (pPrime p) rfl M hsm (continuousH1 (loc) M) (fun x => by rw [mem_continuousH1_iff]; rfl)
  have hdual := finrank_continuousH2_eq_invariants_dualTwist_of_primeLocal (p := p) (pPrime p) rfl M hsm
  rw [hdual, h2, finrank_bot, h0, finrank_bot, zero_add, zero_add] at hEuler

  set π : levelCocycles₁ (loc) M →ₗ[ZMod p] H1 M :=
    (H1π M).hom ∘ₗ (levelCocycles₁ (loc) M).subtype with hπ
  have hrange : LinearMap.range π = continuousH1 (loc) M := by
    rw [hπ, LinearMap.range_comp, Submodule.range_subtype]; rfl
  have hkerle : LinearMap.ker (H1π M).hom ≤ levelCocycles₁ (loc) M := by
    rw [ker_H1π_eq]; exact comap_coboundaries₁_le_levelCocycles₁ M hsm
  have hker : LinearMap.ker π = (LinearMap.ker (H1π M).hom).comap (levelCocycles₁ (loc) M).subtype := by
    rw [hπ, LinearMap.ker_comp]

  have hinj : Function.Injective (d₀₁ M).hom := by
    rw [← LinearMap.ker_eq_bot, d₀₁_ker_eq_invariants, h0]
  have eB : LinearMap.ker (H1π M).hom ≃ₗ[ZMod p] M :=
    (LinearEquiv.ofEq _ _ (ker_H1π_eq M)).trans <|
      (Submodule.comapSubtypeEquivOfLe (coboundaries₁_le_cocycles₁ M)).trans
        (LinearEquiv.ofInjective (d₀₁ M).hom hinj).symm
  have eK : LinearMap.ker π ≃ₗ[ZMod p] M :=
    (LinearEquiv.ofEq _ _ hker).trans <| (Submodule.comapSubtypeEquivOfLe hkerle).trans eB

  have hfg : (levelCocycles₁ (loc) M).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (H1π M).hom
    · exact Module.Finite.iff_fg.1 hH1
    · rw [inf_eq_right.2 hkerle]
      exact Module.Finite.iff_fg.1 (Module.Finite.equiv eB.symm)
  haveI hLfin : FiniteDimensional (ZMod p) (levelCocycles₁ (loc) M) := Module.Finite.iff_fg.2 hfg
  refine ⟨hLfin, ?_⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hrange), hEuler, LinearEquiv.finrank_eq eK] at hrn
  omega

end Count

end S17K3

open S17K3 in
theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (N : Rep k (primeLocalGaloisGroup (pPrime p))) (hN : Module.finrank k N = 1)
    (hcyc : ∀ (σ : primeLocalGaloisGroup (pPrime p)),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ c : ℕ,
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ c) →
          ∀ m : N, N.ρ σ m = (c : k) • m)
    (hsm : ∀ m : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : primeLocalGaloisGroup (pPrime p), primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup →
        N.ρ s m = m)
    (hne : ∃ (g : primeLocalGaloisGroup (pPrime p)) (c : ℕ),
      (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p g ζ = ζ ^ c) ∧
        ∃ m : N, N.ρ g m ≠ (c : k) • m)
    (Z : Submodule k (cocycles₁ N))
    (hZ : ∀ c, c ∈ Z ↔
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup (pPrime p)),
          primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) :
    FiniteDimensional k Z ∧ Module.finrank k Z ≤ 2 := by
  classical
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI : Module.Finite k N := Module.finite_of_finrank_eq_succ hN
  haveI : Module.Finite (ZMod p) k := Module.Finite.of_finite

  set ψ : primeLocalGaloisGroup (pPrime p) →* kˣ := lineChar N with hψdef
  have hρ : ∀ g (m : N), N.ρ g m = (ψ g : k) • m := ρ_apply_eq_lineChar_smul hN
  let φ : N ≃ₗ[k] k := LinearEquiv.ofFinrankEq N k (by rw [hN, Module.finrank_self])
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : N, m₀ ≠ 0 := ⟨φ.symm 1, by simp⟩
  have hψ_of : ∀ g (c : k), N.ρ g m₀ = c • m₀ → (ψ g : k) = c := fun g c h =>
    smul_left_injective k hm₀ ((hρ g m₀).symm.trans h)

  have hsmψ : ∀ a : k, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → (ofChar ψ).ρ s a = a := by
    obtain ⟨F, hF, h⟩ := hsm m₀
    refine fun a => ⟨F, hF, fun s hs => ?_⟩
    rw [ofChar_ρ_apply, hψ_of s 1 (by rw [one_smul]; exact h s hs), one_mul]
  have hneψ : ∃ (g : primeLocalGaloisGroup (pPrime p)) (c : ℕ),
      (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p g ζ = ζ ^ c) ∧ (ψ g : k) ≠ c := by
    obtain ⟨g, c, hc, m, hm⟩ := hne
    refine ⟨g, c, hc, fun h => hm ?_⟩
    rw [hρ, h]

  set M : Rep.{0} (ZMod p) (primeLocalGaloisGroup (pPrime p)) := resRep (R := ZMod p) (ofChar ψ)
    with hMdef
  haveI : FiniteDimensional (ZMod p) M := ‹Module.Finite (ZMod p) k›
  have hMρ : ∀ g (a : M), M.ρ g a = (ψ g : k) * a := fun _ _ => rfl
  have hsmM : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → M.ρ s m = m := hsmψ
  have hι : Function.Injective (algebraMap (ZMod p) k) := (algebraMap (ZMod p) k).injective

  have h0 : M.ρ.invariants = ⊥ := by
    obtain ⟨σ, hσI, c, hc, hc1⟩ :=
      exists_localAut_mem_inertiaSubgroupIn_forall_pow_eq_and_not_modEq_one p hp2
    have hσ : (ψ σ : k) = c := hψ_of σ c (hcyc σ hσI c hc m₀)
    have hc1' : (c : k) ≠ 1 := by
      intro h
      apply hc1
      apply hι
      rw [map_natCast, map_one]
      exact h
    rw [eq_bot_iff]
    intro a ha
    have h1 : (c : k) * a = a := by rw [← hσ, ← hMρ]; exact ha σ
    have h3 : ((c : k) - 1) * a = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hc1'
    · exact (Submodule.mem_bot _).2 h

  have h2 : (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal (pPrime p)))).ρ.invariants = ⊥ := by
    refine invariants_dualTwist_eq_bot_of_finrank_eq_one (k := k)
      ((cycloChar p).comp (primeLocalToGlobal (pPrime p))) M (Module.finrank_self k)
      (fun g a m => by rw [hMρ, hMρ, smul_eq_mul, smul_eq_mul, mul_left_comm]) ?_
    obtain ⟨g, c, hc, hg⟩ := hneψ
    refine ⟨g, 1, fun h => hg ?_⟩
    rw [hMρ, ← natCast_eq_cycloChar_of_forall_pow_eq p g c hc, map_natCast, smul_eq_mul] at h
    simpa using h
  obtain ⟨hfin, hrank⟩ := finrank_levelCocycles₁_eq M hsmM h0 h2

  set L : Submodule k (cocycles₁ (ofChar ψ)) := levelCocycles₁ (primeLocalToGlobal (pPrime p)) (ofChar ψ)
    with hLdef
  let Φ := cocyclesLineEquiv φ ψ hρ
  let e₁ : Z ≃ₗ[k] L :=
    { toFun := fun z => ⟨Φ z.1, by
        obtain ⟨F, hF, h⟩ := (hZ z.1).1 z.2
        exact (mem_levelCocycles₁_iff _ _ _).2 ⟨F, hF, fun g s hs => congrArg φ (h g s hs)⟩⟩
      invFun := fun c => ⟨Φ.symm c.1, by
        obtain ⟨F, hF, h⟩ := (mem_levelCocycles₁_iff _ _ _).1 c.2
        exact (hZ _).2 ⟨F, hF, fun g s hs => congrArg φ.symm (h g s hs)⟩⟩
      map_add' := fun z w => Subtype.ext (map_add Φ z.1 w.1)
      map_smul' := fun a z => Subtype.ext (map_smul Φ a z.1)
      left_inv := fun z => Subtype.ext (Φ.symm_apply_apply z.1)
      right_inv := fun c => Subtype.ext (Φ.apply_symm_apply c.1) }
  let e₂ : L ≃ₗ[ZMod p] levelCocycles₁ (primeLocalToGlobal (pPrime p)) M :=
    { toFun := fun c => ⟨cocyclesResEquiv (R := ZMod p) (ofChar ψ) c.1, c.2⟩
      invFun := fun c => ⟨(cocyclesResEquiv (R := ZMod p) (ofChar ψ)).symm c.1, c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite (ZMod p) L := Module.Finite.equiv e₂.symm
  haveI : Module.Finite k L := Module.Finite.of_restrictScalars_finite (ZMod p) k L
  have hZfin : Module.Finite k Z := Module.Finite.equiv e₁.symm
  refine ⟨hZfin, ?_⟩
  haveI : Module.Free k L := Module.Free.of_divisionRing k L
  have hmul := Module.finrank_mul_finrank (ZMod p) k L
  rw [e₂.finrank_eq, hrank] at hmul
  change Module.finrank (ZMod p) k * Module.finrank k L = 2 * Module.finrank (ZMod p) k at hmul
  have hdpos : 0 < Module.finrank (ZMod p) k := Module.finrank_pos
  rw [mul_comm 2] at hmul
  have hL2 : Module.finrank k L = 2 := Nat.eq_of_mul_eq_mul_left hdpos hmul
  rw [e₁.finrank_eq, hL2]

end S_groupCohomology_finrank_cocycles_level_le_two_of_finrank_eq_one_of_not_cyclotomic
end P2MW
export P2MW.S_groupCohomology_finrank_cocycles_level_le_two_of_finrank_eq_one_of_not_cyclotomic (solution)
