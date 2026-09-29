-- Prove2me | solution 1 for groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4b6cd1e6-7020-5891-b075-6f82343f9b10

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_exists_isLevelConstant_three_eq_comp_add_d_of_shortExact
import Theorems.Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Theorems.Thm_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

noncomputable section

namespace AlphaSerre

variable {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

def LC (n : ℕ) {X : Type} (f : (Fin n → G) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g s : Fin n → G, (∀ i, r (s i) ∈ F.fixingSubgroup) → f (g * s) = f g

variable {r S}

lemma LC.comp {n : ℕ} {X Y : Type} {f : (Fin n → G) → X} (hf : LC r S n f) (φ : X → Y) : LC r S n (fun t => φ (f t)) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by show φ (f (g * s)) = φ (f g); rw [h g s hs]⟩

lemma LC.add {n : ℕ} {X : Type} [Add X] {f f' : (Fin n → G) → X} (hf : LC r S n f) (hf' : LC r S n f') : LC r S n (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  rw [Pi.add_apply, Pi.add_apply, h g s fun i => IntermediateField.fixingSubgroup_antitone le_sup_left (hs i),
    h' g s fun i => IntermediateField.fixingSubgroup_antitone le_sup_right (hs i)]

variable (r S) in
lemma LC_zero {n : ℕ} {X : Type} [Zero X] : LC r S n (0 : (Fin n → G) → X) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩

section transport
variable {k : Type} [CommRing k]

lemma d_comp {n : ℕ} {A B : Rep.{0} k G} (φ : A ⟶ B) (f : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (f g)) = fun g => φ.hom (((inhomogeneousCochains A).d n (n + 1)).hom f g) := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  funext g
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add, map_sum]
  congr 1
  · exact (Rep.hom_comm_apply φ (g 0) _).symm
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]

end transport

section fixed
variable {p : ℕ} [Fact p.Prime]

lemma exists_fixed_ne_zero (U : Subgroup G) [U.Normal] (hP : IsPGroup p (G ⧸ U))
    (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M]
    (htriv : ∀ s ∈ U, M.ρ s = 1) (hM : 0 < Module.finrank (ZMod p) M) :
    ∃ m : M, m ≠ 0 ∧ ∀ g, M.ρ g m = m := by
  classical
  let ρbar : G ⧸ U →* Module.End (ZMod p) M := QuotientGroup.lift U M.ρ fun s hs => MonoidHom.mem_ker.mpr (htriv s hs)
  letI : MulAction (G ⧸ U) M := MulAction.compHom M ρbar
  have hsmul : ∀ (g : G) (x : M), (QuotientGroup.mk g : G ⧸ U) • x = M.ρ g x := fun g x => by
    show ρbar (QuotientGroup.mk g) x = M.ρ g x
    rw [QuotientGroup.lift_mk]
  haveI : Finite M := Module.finite_of_finite (ZMod p)
  have hcard : p ∣ Nat.card M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p hM.ne'
  have h0 : (0 : M) ∈ MulAction.fixedPoints (G ⧸ U) M := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hsmul, map_zero]
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hcard h0
  refine ⟨b, fun h => hb0 h.symm, fun g => ?_⟩
  have := hb (QuotientGroup.mk g)
  rwa [hsmul] at this

end fixed

section devissage
variable {p : ℕ} [Fact p.Prime]

theorem devissage (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.comap r).Normal] (hP : IsPGroup p (G ⧸ L.fixingSubgroup.comap r))
    (hlev : ∀ v : (Fin 3 → G) → Rep.trivial (ZMod p) G (ZMod p), LC r S 3 v →
      ((inhomogeneousCochains (Rep.trivial (ZMod p) G (ZMod p))).d 3 4).hom v = 0 →
      ∃ w : (Fin 2 → G) → Rep.trivial (ZMod p) G (ZMod p), LC r S 2 w ∧
        ((inhomogeneousCochains (Rep.trivial (ZMod p) G (ZMod p))).d 2 3).hom w = v) :
    ∀ (n : ℕ) (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M], Module.finrank (ZMod p) M = n →
      (∀ s, r s ∈ L.fixingSubgroup → M.ρ s = 1) →
      ∀ v : (Fin 3 → G) → M, LC r S 3 v → ((inhomogeneousCochains M).d 3 4).hom v = 0 →
        ∃ w : (Fin 2 → G) → M, LC r S 2 w ∧ ((inhomogeneousCochains M).d 2 3).hom w = v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn htriv v hv hdv
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · haveI : Subsingleton M := Module.finrank_zero_iff.mp hn
    refine ⟨0, LC_zero r S, ?_⟩
    rw [map_zero]
    funext t
    exact Subsingleton.elim _ _
  ·
    obtain ⟨m, hm0, hm⟩ := exists_fixed_ne_zero (L.fixingSubgroup.comap r) hP M (fun s hs => htriv s hs) (hn ▸ hpos)
    let W : Submodule (ZMod p) M := (ZMod p) ∙ m
    have hW : ∀ g, W ≤ W.comap (M.ρ g) := fun g =>
      (Submodule.span_singleton_le_iff_mem _ _).mpr (by rw [Submodule.mem_comap, hm g]; exact Submodule.mem_span_singleton_self m)
    let M'' : Rep.{0} (ZMod p) G := Rep.of (M.ρ.quotient W hW)
    let ι : Rep.trivial (ZMod p) G (ZMod p) ⟶ M :=
      Rep.ofHom ⟨LinearMap.toSpanSingleton (ZMod p) M m, fun g => LinearMap.ext fun c => by
        show c • m = M.ρ g (c • m)
        rw [map_smul, hm g]⟩
    let π : M ⟶ M'' := Rep.ofHom ⟨W.mkQ, fun g => LinearMap.ext fun x => rfl⟩
    have hιa : ∀ c, ι.hom c = c • m := fun _ => rfl
    have hπa : ∀ x, π.hom x = W.mkQ x := fun _ => rfl
    have hι : Function.Injective ι.hom := fun c c' h => by
      rw [hιa, hιa] at h
      exact smul_left_injective (ZMod p) hm0 h
    have hπ : Function.Surjective π.hom := fun y => by
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W y
      exact ⟨x, rfl⟩
    have hex : Function.Exact ι.hom π.hom := by
      intro x
      constructor
      · intro hx
        have hx' : x ∈ W := by rwa [hπa, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx'
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        rw [hιa, hπa, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self m)
    have hsmM : ∀ x : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s x = x :=
      fun x => ⟨L, hL, fun s hs => by rw [htriv s hs]; rfl⟩

    have hfinW : Module.finrank (ZMod p) W = 1 := finrank_span_singleton hm0
    have hfin'' : Module.finrank (ZMod p) (M ⧸ W) = n - 1 := by
      have := Submodule.finrank_quotient_add_finrank W
      omega
    have htriv'' : ∀ s, r s ∈ L.fixingSubgroup → M''.ρ s = 1 := fun s hs => by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W y
      show W.mkQ (M.ρ s x) = W.mkQ x
      rw [htriv s hs]; rfl
    have hv'' : LC r S 3 (fun t => π.hom (v t)) := hv.comp _
    have hdv'' : ((inhomogeneousCochains M'').d 3 4).hom (fun t => π.hom (v t)) = 0 := by
      rw [d_comp π v, hdv]; funext t; exact map_zero _
    obtain ⟨b'', hb''lc, hdb''⟩ := ih (n - 1) (by omega) M'' hfin'' htriv'' _ hv'' hdv''

    obtain ⟨v', b, hv'lc, hv'coc, hblc, hdec⟩ :=
      groupCohomology.exists_isLevelConstant_three_eq_comp_add_d_of_shortExact r S ι π hι hπ hex hsmM v hv hdv b'' hb''lc hdb''.symm

    obtain ⟨w₁, hw₁lc, hdw₁⟩ := hlev v' hv'lc hv'coc
    refine ⟨(fun t => ι.hom (w₁ t)) + b, (LC.comp hw₁lc _).add hblc, ?_⟩
    rw [map_add, d_comp ι w₁, hdw₁, hdec]

end devissage

end AlphaSerre

end

local instance AlphaSerre.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance AlphaSerre.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance AlphaSerre.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance AlphaSerre.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace AlphaSerre

lemma fixingSubgroup_normal (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [hF : Normal ℚ F] : F.fixingSubgroup.Normal := by
  refine ⟨fun s hs g => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hgx : g⁻¹ x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 hF g⁻¹) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hgx]
  simp

lemma d_res {k : Type} [CommRing k] {G H : Type} [Group G] [Group H] (f : G →* H) (A : Rep.{0} k H) {n : ℕ}
    (w : (Fin n → H) → A) :
    ((inhomogeneousCochains (Rep.res f A)).d n (n + 1)).hom (fun t => w (fun i => f (t i))) =
      fun t => ((inhomogeneousCochains A).d n (n + 1)).hom w (fun i => f (t i)) := by
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
  funext t
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ h]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_eq _ _ _ _ h, map_mul]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.contractNth_apply_of_gt _ _ _ _ h]

end AlphaSerre

set_option maxHeartbeats 6400000 in
open AlphaSerre in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hlev : ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)), K.IsUnramifiedOutside S → FiniteDimensional ℚ ↥K →
      (∀ s ∈ K.fixingSubgroup, cycloChar p s = 1) →
      ∀ u : (Fin 3 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 3 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → u (g * s) = u g) →
        ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 3 4).hom u = 0 →
        ∃ w : (Fin 2 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 2 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
          ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 2 3).hom w = u)
    (N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) N]
    (hsm : ∀ m : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N.ρ s = 1)
    (u : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ i, s i ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0) :
    ∃ w : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ i, s i ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains N).d 2 3).hom w = u := by
  classical

  obtain ⟨L₁, hL₁, hN₁⟩ := groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S N hsm hur
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hL₂ : (IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))).IsUnramifiedOutside S :=
    IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow S hpS 0 ζ (by rwa [zero_add, pow_one])
  obtain ⟨L, hle, hL, hLn⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S _ (hL₁.sup hL₂)
  haveI := hLn
  haveI : FiniteDimensional ℚ ↥L := hL.1
  haveI hΓLn : L.fixingSubgroup.Normal := fixingSubgroup_normal L
  have hNL : ∀ s ∈ L.fixingSubgroup, N.ρ s = 1 :=
    fun s hs => hN₁ s (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle) hs)
  have hχL : ∀ s ∈ L.fixingSubgroup, cycloChar p s = 1 := fun s hs =>
    ExtCitation.cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem _ ζ hζ (IntermediateField.mem_adjoin_simple_self ℚ ζ) s
      (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle) hs)

  haveI : L.fixingSubgroup.FiniteIndex := by
    refine ⟨fun h0 => ?_⟩
    have h1 : L.fixingSubgroup.index ≠ 0 := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'
    exact h1 h0
  haveI : Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)))
  let H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := (P : Subgroup _).comap (QuotientGroup.mk' L.fixingSubgroup)
  have hHmem : ∀ s, s ∈ H ↔ (QuotientGroup.mk s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup) ∈ (P : Subgroup _) :=
    fun s => Iff.rfl
  have hLH : L.fixingSubgroup ≤ H := fun s hs => by
    rw [hHmem, (QuotientGroup.eq_one_iff s).mpr hs]; exact one_mem _

  have hpowL : ∀ s ∈ H, s ^ (p ^ (Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)).factorization p) ∈ L.fixingSubgroup := by
    intro s hs
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← Sylow.card_eq_multiplicity P]
    have h := pow_card_eq_one' (G := ↥(P : Subgroup ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)))
      (x := ⟨QuotientGroup.mk s, (hHmem s).mp hs⟩)
    exact congrArg Subtype.val h

  have hHopen : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hLH (IntermediateField.fixingSubgroup_isOpen L)
  have hHclosed : IsClosed (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := Subgroup.isClosed_of_isOpen H hHopen
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField H
  have hKH : K.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  haveI : FiniteDimensional ℚ ↥K := (InfiniteGalois.isOpen_iff_finite K).mp (by rw [hKH]; exact hHopen)
  have hK : K.IsUnramifiedOutside S :=
    ⟨inferInstance, fun q hq A hA => ((hL.2 q hq A hA).trans hLH).trans hKH.ge⟩
  haveI hKfi : K.fixingSubgroup.FiniteIndex := by
    rw [hKH]
    refine ⟨fun h0 => ?_⟩
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h0
    exact Subgroup.FiniteIndex.index_ne_zero h0
  have hpK : ¬ p ∣ K.fixingSubgroup.index := by
    rw [hKH, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact P.not_dvd_index

  have hcop : Nat.Coprime (p ^ (Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)).factorization p) (p - 1) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_self_sub_right (Fact.out : p.Prime).one_le).mpr (Nat.coprime_one_right p))
  have hKζ : ∀ s ∈ K.fixingSubgroup, cycloChar p s = 1 := by
    intro s hs
    rw [hKH] at hs
    have h1 : (cycloChar p s) ^ (p ^ (Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)).factorization p) = 1 := by
      rw [← map_pow]; exact hχL _ (hpowL s hs)
    have h2 : (cycloChar p s) ^ (p - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one p _
    have h := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h

  haveI hUn : (L.fixingSubgroup.comap K.fixingSubgroup.subtype).Normal := hΓLn.comap _
  have hPK : IsPGroup p (↥K.fixingSubgroup ⧸ L.fixingSubgroup.comap K.fixingSubgroup.subtype) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨(Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ L.fixingSubgroup)).factorization p, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, map_pow]
    exact hpowL _ (hKH ▸ g.2)
  have htriv₀ : ∀ s : ↥K.fixingSubgroup, K.fixingSubgroup.subtype s ∈ L.fixingSubgroup →
      (Rep.res K.fixingSubgroup.subtype N).ρ s = 1 := fun s hs => hNL _ hs
  have hlevK : ∀ v : (Fin 3 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
      LC K.fixingSubgroup.subtype S 3 v →
      ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 3 4).hom v = 0 →
      ∃ w : (Fin 2 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p), LC K.fixingSubgroup.subtype S 2 w ∧
        ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 2 3).hom w = v :=
    fun v hv hdv => hlev K hK inferInstance hKζ v hv hdv

  have hvlc : LC K.fixingSubgroup.subtype S 3 (fun t : Fin 3 → ↥K.fixingSubgroup => u (fun i => K.fixingSubgroup.subtype (t i))) := by
    obtain ⟨F, hF, h⟩ := hlc
    exact ⟨F, hF, fun g s hs => h (fun i => K.fixingSubgroup.subtype (g i)) (fun i => K.fixingSubgroup.subtype (s i)) hs⟩
  have hvcoc : ((inhomogeneousCochains (Rep.res K.fixingSubgroup.subtype N)).d 3 4).hom
      (fun t : Fin 3 → ↥K.fixingSubgroup => u (fun i => K.fixingSubgroup.subtype (t i))) = 0 := by
    rw [d_res K.fixingSubgroup.subtype N u, hcoc]; rfl
  obtain ⟨w', hw'lc, hdw'⟩ := devissage (r := K.fixingSubgroup.subtype) (S := S) L hL hPK hlevK _
    (Rep.res K.fixingSubgroup.subtype N) rfl htriv₀ _ hvlc hvcoc

  exact groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three S N K hK hpK u hlc hcoc w' hw'lc hdw'

end S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
end P2MW
export P2MW.S_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel (solution)
