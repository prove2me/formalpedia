-- Prove2me | solution 1 for groupCohomology.H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9e5c6611-124e-5777-8c16-cc97c814cf17

import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_ModularCurve_SL2Elementary
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_subfield_specialLinearGroup_conj_le_of_dvd_card
import Theorems.Thm_groupCohomology_subsingleton_H1_of_isUnit_card
import Theorems.Thm_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index
import Theorems.Thm_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
import Theorems.Thm_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range

set_option autoImplicit false

open groupCohomology Matrix MatrixGroups

namespace P2mH1piV

section Generic

variable {R G : Type} [CommRing R] [Group G]

lemma exists_eq_sub_of_subsingleton_H1 (A : Rep.{0} R G) [Subsingleton (H1 A)]
    (x : cocycles₁ A) : ∃ m : A, ∀ g : G, x g = A.ρ g m - m := by
  have hx : H1π A x = 0 := Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  refine ⟨m, fun g => ?_⟩
  have := congrFun hm g
  rw [← this]
  rfl

lemma H1π_eq_zero_of_exists (A : Rep.{0} R G) (x : cocycles₁ A)
    (h : ∃ m : A, ∀ g : G, x g = A.ρ g m - m) : H1π A x = 0 := by
  rw [H1π_eq_zero_iff]
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  funext g
  rw [hm g]
  rfl

end Generic

section SL2

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

open ModularCurve

lemma units_eq_one_of_pow_eq_one (u : (ZMod p)ˣ) (hu : u ^ p = 1) : u = 1 := by
  have h2 : u ^ (p - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one p u
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le
  calc u = u ^ (p - 1 + 1) := by rw [pow_succ, h2, one_mul]
    _ = 1 := by rw [hp, hu]

lemma hom_upperElem (φ : SL(2, F) →* (ZMod p)ˣ) (b : F) : φ (upperElem b) = 1 := by
  apply units_eq_one_of_pow_eq_one
  rw [← map_pow, upperElem_pow, CharP.cast_eq_zero, zero_mul, upperElem_zero, map_one]

lemma hom_lowerElem (φ : SL(2, F) →* (ZMod p)ˣ) (c : F) : φ (lowerElem c) = 1 := by
  apply units_eq_one_of_pow_eq_one
  rw [← map_pow, lowerElem_pow, CharP.cast_eq_zero, zero_mul, lowerElem_zero, map_one]

lemma sl2_eq_of_ne_zero (a b c d : F) (hdet : a * d - b * c = 1) (hc : c ≠ 0) :
    (⟨!![a, b; c, d], by rwa [Matrix.det_fin_two_of]⟩ : SL(2, F)) =
      upperElem ((a - 1) / c) * lowerElem c * upperElem ((d - 1) / c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination (-1 : F) * hdet

lemma hom_sl2_eq_one (φ : SL(2, F) →* (ZMod p)ˣ) (M : SL(2, F)) : φ M = 1 := by

  have key : ∀ M : SL(2, F), M 1 0 ≠ 0 → φ M = 1 := by
    intro M hM
    induction M using Matrix.SpecialLinearGroup.fin_two_induction with
    | h a b c d hdet =>
      have hc : c ≠ 0 := by simpa using hM
      rw [sl2_eq_of_ne_zero a b c d hdet hc, map_mul, map_mul, hom_upperElem, hom_lowerElem,
        hom_upperElem, one_mul, one_mul]
  by_cases hM : M 1 0 ≠ 0
  · exact key M hM
  · push Not at hM
    have h1 : (lowerElem (1 : F) * M) 1 0 ≠ 0 := by
      induction M using Matrix.SpecialLinearGroup.fin_two_induction with
      | h a b c d hdet =>
        have hc : c = 0 := by simpa using hM
        subst hc
        have ha : a ≠ 0 := by
          rintro rfl; simp at hdet
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using ha
    have := key _ h1
    rwa [map_mul, hom_lowerElem, one_mul] at this

end SL2

section Descent

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime]
  {V : Type} [AddCommGroup V] [Module k V]
  {G : Type} [Group G] (ρ : G →* Module.End k V)
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k V))]
  (ρ₀ : Representation (ZMod p) G (LinearMap.ker (LinearMap.trace k V)))
  (hρ₀ : ∀ (g : G) (f : LinearMap.ker (LinearMap.trace k V)),
      ((ρ₀ g f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) = ρ g * f * ρ g⁻¹)
  (χ : G →* (ZMod p)ˣ) (hχ₀ : ∀ g : G, ρ₀ g = 1 → χ g = 1)

abbrev N : Subgroup G := ρ.toHomUnits.ker

lemma mem_N_iff (g : G) : g ∈ N ρ ↔ ρ g = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one, MonoidHom.coe_toHomUnits]

lemma map_inv_eq_one_of {g : G} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := map_mul ρ g⁻¹ g
  rwa [inv_mul_cancel, map_one, hg, mul_one, eq_comm] at this

abbrev Q : Type := G ⧸ N ρ

noncomputable def ρu : Q ρ →* (Module.End k V)ˣ := QuotientGroup.kerLift ρ.toHomUnits

noncomputable def ρ₁ : Q ρ →* Module.End k V := (Units.coeHom _).comp (ρu ρ)

@[scoped simp] lemma ρ₁_mk (g : G) : ρ₁ ρ (g : Q ρ) = ρ g := rfl

lemma ρ₁_injective : Function.Injective (ρ₁ ρ) :=
  Units.val_injective.comp (QuotientGroup.kerLift_injective _)

include hρ₀ in
lemma ρ₀_eq_one_of {g : G} (hg : ρ g = 1) : ρ₀ g = 1 := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  change ((ρ₀ g f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) = f
  rw [hρ₀, hg, map_inv_eq_one_of ρ hg, one_mul, mul_one]

include hρ₀ in
lemma N_le_ker_ρ₀ : N ρ ≤ ρ₀.ker := fun g hg =>
  (MonoidHom.mem_ker).2 (ρ₀_eq_one_of ρ ρ₀ hρ₀ ((mem_N_iff ρ g).1 hg))

include hρ₀ hχ₀ in
lemma N_le_ker_χ : N ρ ≤ χ.ker := fun g hg =>
  (MonoidHom.mem_ker).2 (hχ₀ g (ρ₀_eq_one_of ρ ρ₀ hρ₀ ((mem_N_iff ρ g).1 hg)))

noncomputable def ρ₀₁ : Representation (ZMod p) (Q ρ) (LinearMap.ker (LinearMap.trace k V)) :=
  QuotientGroup.lift (N ρ) ρ₀ (N_le_ker_ρ₀ ρ ρ₀ hρ₀)

@[scoped simp] lemma ρ₀₁_mk (g : G) : ρ₀₁ ρ ρ₀ hρ₀ (g : Q ρ) = ρ₀ g :=
  QuotientGroup.lift_mk _ _ _

lemma ρ₀₁_apply_coe (q : Q ρ) (f : LinearMap.ker (LinearMap.trace k V)) :
    ((ρ₀₁ ρ ρ₀ hρ₀ q f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) =
      ρ₁ ρ q * f * ρ₁ ρ q⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [ρ₀₁_mk, hρ₀, ← QuotientGroup.mk_inv, ρ₁_mk, ρ₁_mk]

noncomputable def χ₁ : Q ρ →* (ZMod p)ˣ := QuotientGroup.lift (N ρ) χ (N_le_ker_χ ρ ρ₀ hρ₀ χ hχ₀)

@[scoped simp] lemma χ₁_mk (g : G) : χ₁ ρ ρ₀ hρ₀ χ hχ₀ (g : Q ρ) = χ g :=
  QuotientGroup.lift_mk _ _ _

lemma χ₁_eq_one_of (q : Q ρ) (hq : ρ₀₁ ρ ρ₀ hρ₀ q = 1) : χ₁ ρ ρ₀ hρ₀ χ hχ₀ q = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [ρ₀₁_mk] at hq
  rw [χ₁_mk, hχ₀ g hq]

noncomputable abbrev M₁ : Rep (ZMod p) (Q ρ) := (Rep.of (ρ₀₁ ρ ρ₀ hρ₀)).dualTwist (χ₁ ρ ρ₀ hρ₀ χ hχ₀)

lemma M₁_ρ_mk (g : G) (f : Module.Dual (ZMod p) (LinearMap.ker (LinearMap.trace k V))) :
    (M₁ ρ ρ₀ hρ₀ χ hχ₀).ρ (g : Q ρ) f = ((Rep.of ρ₀).dualTwist χ).ρ g f := by
  change ((χ₁ ρ ρ₀ hρ₀ χ hχ₀ (g : Q ρ) : ZMod p)) • (f ∘ₗ ρ₀₁ ρ ρ₀ hρ₀ (g : Q ρ)⁻¹) =
    (χ g : ZMod p) • (f ∘ₗ ρ₀ g⁻¹)
  rw [χ₁_mk, ← QuotientGroup.mk_inv, ρ₀₁_mk]

variable (c : cocycles₁ ((Rep.of ρ₀).dualTwist χ)) (hc : ∀ g : G, ρ₀ g = 1 → c g = 0)

include hρ₀ in
lemma c_mul_of_mem_N (hc : ∀ g : G, ρ₀ g = 1 → c g = 0) (g n : G) (hn : n ∈ N ρ) :
    c (g * n) = c g := by
  rw [(mem_cocycles₁_iff c).1 c.2, hc n (ρ₀_eq_one_of ρ ρ₀ hρ₀ ((mem_N_iff ρ n).1 hn)), map_zero,
    zero_add]

noncomputable def c₁ : cocycles₁ (M₁ ρ ρ₀ hρ₀ χ hχ₀) :=
  ⟨fun q => c q.out, by
    have hmk : ∀ g : G, c ((g : Q ρ).out) = c g := by
      intro g
      obtain ⟨h, H⟩ := QuotientGroup.mk_out_eq_mul (N ρ) g
      rw [H, c_mul_of_mem_N ρ ρ₀ hρ₀ χ c hc g h h.2]
    rw [mem_cocycles₁_iff]
    intro q q'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
    change c ((g : Q ρ) * (g' : Q ρ)).out = _
    rw [← QuotientGroup.mk_mul, hmk, hmk, hmk, M₁_ρ_mk, (mem_cocycles₁_iff c).1 c.2]⟩

lemma c₁_mk (g : G) : c₁ ρ ρ₀ hρ₀ χ hχ₀ c hc (g : Q ρ) = c g := by
  change c ((g : Q ρ).out) = c g
  obtain ⟨h, H⟩ := QuotientGroup.mk_out_eq_mul (N ρ) g
  rw [H, c_mul_of_mem_N ρ ρ₀ hρ₀ χ c hc g h h.2]

include hc in

theorem H1π_eq_zero_of_subsingleton (hM : Subsingleton (H1 (M₁ ρ ρ₀ hρ₀ χ hχ₀))) :
    H1π ((Rep.of ρ₀).dualTwist χ) c = 0 := by
  obtain ⟨m, hm⟩ := exists_eq_sub_of_subsingleton_H1 _ (c₁ ρ ρ₀ hρ₀ χ hχ₀ c hc)
  apply H1π_eq_zero_of_exists
  refine ⟨m, fun g => ?_⟩
  have := hm (g : Q ρ)
  rwa [c₁_mk, M₁_ρ_mk] at this

lemma finite_Q (hfin : (Set.range ρ).Finite) : Finite (Q ρ) := by
  have h1 : (Set.range ρ.toHomUnits).Finite := by
    apply Set.Finite.of_finite_image (f := (Units.val : (Module.End k V)ˣ → Module.End k V))
    · apply hfin.subset
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · exact Units.val_injective.injOn
  have h2 : Finite ρ.toHomUnits.range := h1.to_subtype
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ.toHomUnits).toEquiv.symm

end Descent

section Coordinates

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime]
  {V : Type} [AddCommGroup V] [Module k V]
  {G : Type} [Group G]

lemma finiteDimensional_V (hV : Module.finrank k V = 2) : FiniteDimensional k V :=
  Module.finite_of_finrank_pos (by omega)

noncomputable def basis (hV : Module.finrank k V = 2) : Module.Basis (Fin 2) k V :=
  haveI := finiteDimensional_V hV
  Module.finBasisOfFinrankEq k V hV

variable (hV : Module.finrank k V = 2) (ρ : G →* Module.End k V)

noncomputable def ρGL : Q ρ →* GL (Fin 2) k :=
  (Units.map ((LinearMap.toMatrixAlgEquiv (basis hV) :
    Module.End k V ≃ₐ[k] Matrix (Fin 2) (Fin 2) k) : Module.End k V →* Matrix (Fin 2) (Fin 2) k)).comp
    (ρu ρ)

lemma ρGL_coe (q : Q ρ) :
    ((ρGL hV ρ q : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      LinearMap.toMatrix (basis hV) (basis hV) (ρ₁ ρ q) := rfl

lemma ρGL_injective : Function.Injective (ρGL hV ρ) := by
  intro q q' h
  apply ρ₁_injective ρ
  apply (LinearMap.toMatrix (basis hV) (basis hV)).injective
  rw [← ρGL_coe, ← ρGL_coe, h]

noncomputable abbrev H : Subgroup (GL (Fin 2) k) := (ρGL hV ρ).range

noncomputable def equivH : Q ρ ≃* H hV ρ := MonoidHom.ofInjective (ρGL_injective hV ρ)

lemma finite_H [Finite (Q ρ)] : Finite (H hV ρ) := Finite.of_equiv _ (equivH hV ρ).toEquiv

lemma card_H : Nat.card (H hV ρ) = Nat.card (Q ρ) := (Nat.card_congr (equivH hV ρ).toEquiv).symm

lemma hirr_H (χ : G →* (ZMod p)ˣ)
    (hirr : ∀ W : Submodule k V, (∀ g : G, χ g = 1 → ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (v : Fin 2 → k) (hv : v ≠ 0) :
    ∃ h ∈ H hV ρ, ((h : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∉ k ∙ v := by
  by_contra! habs
  set b := basis hV
  set x : V := b.equivFun.symm v with hx
  have hbx : ⇑(b.repr x) = v := by
    funext i; rw [hx, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hv
    rw [← hbx, h0, map_zero]
    rfl
  set W : Submodule k V := k ∙ x
  have hW : ∀ g : G, ∀ y ∈ W, ρ g y ∈ W := by
    intro g y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_smul]
    apply Submodule.smul_mem

    have hmem := habs (ρGL hV ρ (g : Q ρ)) ⟨(g : Q ρ), rfl⟩
    rw [ρGL_coe, ρ₁_mk, ← hbx, LinearMap.toMatrix_mulVec_repr] at hmem
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
    have : ρ g x = s • x := by
      apply b.repr.injective
      apply DFunLike.coe_injective
      change ⇑((basis hV).repr ((ρ g) x)) = ⇑(b.repr (s • x))
      rw [← hs, map_smul, Finsupp.coe_smul, hbx]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  rcases hirr W (fun g _ => hW g) with hbot | htop
  · exact hx0 ((Submodule.span_singleton_eq_bot).1 hbot)
  · have h1 : Module.finrank k W ≤ 1 := by
      rw [finrank_span_singleton hx0]
    rw [htop, finrank_top, hV] at h1
    omega

end Coordinates

section BranchSL

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime]
  {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
  {G : Type} [Group G] (ρ : G →* Module.End k V)
  (F : Subfield k) (g : GL (Fin 2) k)

noncomputable def ψ : SL(2, F) →* GL (Fin 2) k :=
  (MulAut.conj g).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map F.subtype))

lemma ψ_apply (m : SL(2, F)) :
    ψ F g m = g * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map F.subtype m) * g⁻¹ :=
  rfl

lemma ψ_coe (m : SL(2, F)) :
    ((ψ F g m : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  rw [ψ_apply, Units.val_mul, Units.val_mul]
  rfl

noncomputable def S : Subgroup (Q ρ) := (ψ F g).range.comap (ρGL hV ρ)

lemma mem_S_iff (q : Q ρ) : q ∈ S hV ρ F g ↔ ∃ m : SL(2, F), ψ F g m = ρGL hV ρ q := Iff.rfl

variable (hSL : ∀ s : SL(2, F),
    g * (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map F.subtype s)) * g⁻¹ ∈ H hV ρ)

noncomputable def θ : SL(2, F) →* Q ρ :=
  (equivH hV ρ).symm.toMonoidHom.comp ((ψ F g).codRestrict (H hV ρ) hSL)

lemma ρGL_θ (m : SL(2, F)) : ρGL hV ρ (θ hV ρ F g hSL m) = ψ F g m := by
  have : ((equivH hV ρ) (θ hV ρ F g hSL m) : GL (Fin 2) k) = ψ F g m := by
    change ((equivH hV ρ) ((equivH hV ρ).symm ⟨ψ F g m, hSL m⟩) : GL (Fin 2) k) = ψ F g m
    rw [MulEquiv.apply_symm_apply]
  rw [← this]
  rfl

lemma θ_mem_S (m : SL(2, F)) : θ hV ρ F g hSL m ∈ S hV ρ F g :=
  ⟨m, (ρGL_θ hV ρ F g hSL m).symm⟩

lemma exists_eq_θ_of_mem_S {q : Q ρ} (hq : q ∈ S hV ρ F g) : ∃ m : SL(2, F), q = θ hV ρ F g hSL m := by
  obtain ⟨m, hm⟩ := hq
  exact ⟨m, ρGL_injective hV ρ (by rw [ρGL_θ, hm])⟩

end BranchSL

section Numerics

variable {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
  {G : Type} [Group G] (ρ : G →* Module.End k V)
  [Module (ZMod p) (LinearMap.ker (LinearMap.trace k V))]
  (ρ₀ : Representation (ZMod p) G (LinearMap.ker (LinearMap.trace k V)))
  (hρ₀ : ∀ (g : G) (f : LinearMap.ker (LinearMap.trace k V)),
      ((ρ₀ g f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) = ρ g * f * ρ g⁻¹)
  (χ : G →* (ZMod p)ˣ) (hχ₀ : ∀ g : G, ρ₀ g = 1 → χ g = 1)

omit [Finite k] in

lemma ρ₁_eq_smul_of_scalar {x : Q ρ} {a : k}
    (hx : ((ρGL hV ρ x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k)) :
    ρ₁ ρ x = a • (1 : Module.End k V) := by
  apply (LinearMap.toMatrix (basis hV) (basis hV)).injective
  rw [← ρGL_coe, hx, map_smul, LinearMap.toMatrix_one]

omit [Finite k] in
lemma ne_zero_of_scalar {x : Q ρ} {a : k}
    (hx : ((ρGL hV ρ x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k)) :
    a ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hx
  exact Units.ne_zero _ hx

omit [Finite k] [CharP k p] in
include hρ₀ in

lemma χ₁_eq_one_of_scalar {x : Q ρ} {a : k}
    (hx : ((ρGL hV ρ x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k)) :
    χ₁ ρ ρ₀ hρ₀ χ hχ₀ x = 1 := by
  apply χ₁_eq_one_of
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [ρ₀₁_apply_coe, ρ₁_eq_smul_of_scalar hV ρ hx, smul_mul_assoc, one_mul, smul_mul_assoc,
    ← mul_smul_comm, ← smul_one_mul a (ρ₁ ρ x⁻¹), ← ρ₁_eq_smul_of_scalar hV ρ hx, ← map_mul,
    mul_inv_cancel, map_one, mul_one]
  rfl

lemma pow_card_sub_one_of_scalar {x : Q ρ} {a : k}
    (hx : ((ρGL hV ρ x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k)) :
    x ^ (Nat.card k - 1) = 1 := by
  letI : Fintype k := Fintype.ofFinite k
  apply ρGL_injective hV ρ
  apply Units.ext
  rw [map_pow, Units.val_pow_eq_pow_val, hx, smul_pow, one_pow, Nat.card_eq_fintype_card,
    FiniteField.pow_card_sub_one_eq_one a (ne_zero_of_scalar hV ρ hx), one_smul, map_one, Units.val_one]

variable (F : Subfield k) (g : GL (Fin 2) k)
  (hSL : ∀ s : SL(2, F),
    g * (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map F.subtype s)) * g⁻¹ ∈ H hV ρ)
  (hH : ∀ h ∈ H hV ρ, ∃ (a : k) (m : GL (Fin 2) F),
    ((g⁻¹ * h * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      a • ((Matrix.GeneralLinearGroup.map F.subtype m : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))

omit [Finite k] [CharP k p] in
lemma map_subtype_smul (r : F) (A : Matrix (Fin 2) (Fin 2) F) :
    (r • A).map F.subtype = (r : k) • A.map F.subtype := by
  ext i j; simp [Matrix.map_apply]

omit [Finite k] [CharP k p] in
lemma conj_mul_conj (A B : Matrix (Fin 2) (Fin 2) k) :
    ((g : Matrix (Fin 2) (Fin 2) k) * A * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) *
      ((g : Matrix (Fin 2) (Fin 2) k) * B * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) =
      (g : Matrix (Fin 2) (Fin 2) k) * (A * B) * ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

omit [Finite k] [CharP k p] in

lemma coe_eq_of_hH {h : GL (Fin 2) k} {a : k} {m : GL (Fin 2) F}
    (hm : ((g⁻¹ * h * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      a • ((Matrix.GeneralLinearGroup.map F.subtype m : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) :
    (h : Matrix (Fin 2) (Fin 2) k) =
      (g : Matrix (Fin 2) (Fin 2) k) * (a • (m : Matrix (Fin 2) (Fin 2) F).map F.subtype) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  have : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
  conv_lhs => rw [this]
  rw [Units.val_mul, Units.val_mul, hm]
  rfl

omit [Finite k] in
include hH in

lemma exists_sq_mul_scalar (q : Q ρ) : ∃ (m' : SL(2, F)) (c : k),
    ((ρGL hV ρ (q ^ 2 * (θ hV ρ F g hSL m')⁻¹) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      c • (1 : Matrix (Fin 2) (Fin 2) k) := by
  obtain ⟨a, m, hm⟩ := hH (ρGL hV ρ q) ⟨q, rfl⟩
  set M : Matrix (Fin 2) (Fin 2) F := (m.val : Matrix (Fin 2) (Fin 2) F) with hMdef
  set d : F := M.det with hd
  have hd0 : d ≠ 0 := by
    rw [hd, hMdef, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  let m' : SL(2, F) := ⟨d⁻¹ • (M * M), by
    rw [Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, ← hd]; field_simp⟩
  refine ⟨m', a ^ 2 * (d : k), ?_⟩
  have hh := coe_eq_of_hH F g hm
  have hd0' : (d : k) ≠ 0 := fun h0 => hd0 (by exact_mod_cast h0)

  have hsq : ((ρGL hV ρ q ^ 2 : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (a ^ 2 * (d : k)) • ((ψ F g m' : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    rw [Units.val_pow_eq_pow_val, hh, sq, conj_mul_conj, ψ_coe, ← Matrix.smul_mul,
      ← Matrix.mul_smul]
    congr 2
    change _ = (a ^ 2 * (d : k)) • ((d⁻¹ • (M * M)).map F.subtype)
    rw [map_subtype_smul, Matrix.map_mul, smul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Subfield.coe_inv, mul_assoc, mul_inv_cancel₀ hd0', mul_one, sq]
  rw [map_mul, map_inv, map_pow, ρGL_θ, Units.val_mul, hsq, Matrix.smul_mul, Units.mul_inv]

variable [CharP F p]

omit [CharP k p] [Finite k] in
include hSL hH in

lemma χ₁_sq (q : Q ρ) : χ₁ ρ ρ₀ hρ₀ χ hχ₀ q ^ 2 = 1 := by
  obtain ⟨m', c, hz⟩ := exists_sq_mul_scalar hV ρ F g hSL hH q
  have h1 := χ₁_eq_one_of_scalar hV ρ ρ₀ hρ₀ χ hχ₀ hz
  have h2 : χ₁ ρ ρ₀ hρ₀ χ hχ₀ (θ hV ρ F g hSL m') = 1 :=
    hom_sl2_eq_one ((χ₁ ρ ρ₀ hρ₀ χ hχ₀).comp (θ hV ρ F g hSL)) m'
  rw [map_mul, map_inv, h2, inv_one, mul_one, map_pow] at h1
  exact h1

omit [CharP k p] [Finite k] in
include hV hρ₀ hχ₀ hSL hH in

lemma p_eq_three (hp2 : p ≠ 2) (hχ : Function.Surjective χ) : p = 3 := by
  have hp : p.Prime := Fact.out
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    rcases (Nat.prime_two.eq_one_or_self_of_dvd p this) with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp2 h1
  obtain ⟨x, hx⟩ := hχ (Units.mk0 (2 : ZMod p) h20)
  have hsq := χ₁_sq hV ρ ρ₀ hρ₀ χ hχ₀ F g hSL hH (x : Q ρ)
  rw [χ₁_mk, hx, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at hsq
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hsq
  rw [ZMod.natCast_eq_zero_iff] at h3
  rcases (Nat.prime_three.eq_one_or_self_of_dvd p h3) with h1 | h1
  · exact absurd h1 hp.one_lt.ne'
  · exact h1

omit [CharP F p] [Finite k] [CharP k p] in
include hH in

lemma S_normal : (S hV ρ F g).Normal := by
  refine ⟨fun s hs q => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hs
  obtain ⟨a, m, hm⟩ := hH (ρGL hV ρ q) ⟨q, rfl⟩
  set M : Matrix (Fin 2) (Fin 2) F := (m.val : Matrix (Fin 2) (Fin 2) F) with hMdef
  set M' : Matrix (Fin 2) (Fin 2) F := ((m⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM'def
  have hMM' : M * M' = 1 := by rw [hMdef, hM'def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM'M : M' * M = 1 := by rw [hMdef, hM'def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let m₁ : SL(2, F) := ⟨M * (m₀ : Matrix (Fin 2) (Fin 2) F) * M', by
    rw [Matrix.det_mul, Matrix.det_mul, m₀.prop, mul_one, ← Matrix.det_mul, hMM', Matrix.det_one]⟩
  refine ⟨m₁, ?_⟩
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hm
    exact Units.ne_zero _ hm
  have hh := coe_eq_of_hH F g hm

  have hhinv : (((ρGL hV ρ q)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (g : Matrix (Fin 2) (Fin 2) k) * (a⁻¹ • M'.map F.subtype) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hh, conj_mul_conj, smul_mul_smul_comm, mul_inv_cancel₀ ha, one_smul,
      ← Matrix.map_mul, hMM', Matrix.map_one F.subtype (map_zero _) (map_one _), mul_one,
      Units.mul_inv]
  apply Units.ext
  rw [map_mul, map_mul, map_inv, ← hm₀, Units.val_mul, Units.val_mul, hh, ψ_coe, ψ_coe, hhinv,
    conj_mul_conj, conj_mul_conj]
  congr 2
  change (M * (m₀ : Matrix (Fin 2) (Fin 2) F) * M').map F.subtype =
    (a • M.map F.subtype) * ((m₀ : Matrix (Fin 2) (Fin 2) F).map F.subtype) * (a⁻¹ • M'.map F.subtype)
  rw [Matrix.smul_mul, smul_mul_smul_comm, mul_inv_cancel₀ ha, one_smul, Matrix.map_mul,
    Matrix.map_mul]

omit [Module (ZMod p) (LinearMap.ker (LinearMap.trace k V))] [CharP F p] in
include hH hSL in

lemma not_dvd_index [Finite (Q ρ)] (hp2 : p ≠ 2) : ¬ p ∣ (S hV ρ F g).index := by
  haveI := S_normal hV ρ F g hH
  letI : Fintype (Q ρ ⧸ S hV ρ F g) := Fintype.ofFinite _
  letI : Fintype k := Fintype.ofFinite k
  have hp : p.Prime := Fact.out
  intro hdvd
  change p ∣ Nat.card (Q ρ ⧸ S hV ρ F g) at hdvd
  rw [Nat.card_eq_fintype_card] at hdvd
  obtain ⟨xbar, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  obtain ⟨m', c, hz⟩ := exists_sq_mul_scalar hV ρ F g hSL hH x
  have hzpow := pow_card_sub_one_of_scalar hV ρ hz
  have hθ : ((θ hV ρ F g hSL m' : Q ρ) : Q ρ ⧸ S hV ρ F g) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (θ_mem_S hV ρ F g hSL m')
  have hsq : ((x : Q ρ ⧸ S hV ρ F g)) ^ 2 = ((x ^ 2 * (θ hV ρ F g hSL m')⁻¹ : Q ρ) : Q ρ ⧸ S hV ρ F g) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hθ, inv_one, mul_one, QuotientGroup.mk_pow]
  have hpow : ((x : Q ρ ⧸ S hV ρ F g)) ^ (2 * (Nat.card k - 1)) = 1 := by
    rw [pow_mul, hsq, ← QuotientGroup.mk_pow, hzpow, QuotientGroup.mk_one]
  have hdvd' : p ∣ 2 * (Nat.card k - 1) := by
    rw [← hx]; exact orderOf_dvd_of_pow_eq_one hpow
  rcases hp.dvd_mul.1 hdvd' with h2 | hk
  · rcases Nat.prime_two.eq_one_or_self_of_dvd p h2 with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hp2 h1
  · obtain ⟨n, -, hn⟩ := FiniteField.card k p
    rw [Nat.card_eq_fintype_card, hn] at hk
    have hpk : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
    have h1 : p ∣ p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) := Nat.dvd_sub hpk hk
    have hpos : 1 ≤ p ^ (n : ℕ) := Nat.one_le_pow _ _ hp.pos
    rw [Nat.sub_sub_self hpos] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

omit [Finite k] [CharP k p] in
include hSL in

lemma χ₁_eq_one_of_mem_S {q : Q ρ} (hq : q ∈ S hV ρ F g) : χ₁ ρ ρ₀ hρ₀ χ hχ₀ q = 1 := by
  obtain ⟨m, rfl⟩ := exists_eq_θ_of_mem_S hV ρ F g hSL hq
  exact hom_sl2_eq_one ((χ₁ ρ ρ₀ hρ₀ χ hχ₀).comp (θ hV ρ F g hSL)) m

end Numerics

lemma isUnit_natCast_of_not_dvd {p : ℕ} (hp : p.Prime) {n : ℕ} (h : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : ZMod p) :=
  (ZMod.isUnit_iff_coprime n p).2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h))

theorem main
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
    {G : Type} [Group G] (ρ : G →* Module.End k V) (hfin : (Set.range ρ).Finite)
    (χ : G →* (ZMod p)ˣ) (hχ : Function.Surjective χ)
    (hirr : ∀ W : Submodule k V,
      (∀ g : G, χ g = 1 → ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k V))]
    (ρ₀ : Representation (ZMod p) G (LinearMap.ker (LinearMap.trace k V)))
    (hρ₀ : ∀ (g : G) (f : LinearMap.ker (LinearMap.trace k V)),
      ((ρ₀ g f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) = ρ g * f * ρ g⁻¹)
    (hχ₀ : ∀ g : G, ρ₀ g = 1 → χ g = 1)
    (c : cocycles₁ ((Rep.of ρ₀).dualTwist χ))
    (hc : ∀ g : G, ρ₀ g = 1 → c g = 0) :
    H1π ((Rep.of ρ₀).dualTwist χ) c = 0 := by
  have hp : p.Prime := Fact.out
  haveI hQ : Finite (Q ρ) := finite_Q ρ hfin
  apply H1π_eq_zero_of_subsingleton ρ ρ₀ hρ₀ χ hχ₀ c hc
  by_cases hdvd : p ∣ Nat.card (Q ρ)
  · haveI := finite_H hV ρ
    rcases Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card hp2
        (H hV ρ) (by rwa [card_H]) (hirr_H hV ρ χ hirr) with ⟨hp3, h9⟩ | ⟨F, hF, g, hSL, hH⟩
    ·
      subst hp3
      rw [card_H] at h9
      exact groupCohomology.subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card hV
        h9 (ρ₁ ρ) (ρ₁_injective ρ) (χ₁ ρ ρ₀ hρ₀ χ hχ₀) (M₁ ρ ρ₀ hρ₀ χ hχ₀) (LinearEquiv.refl _ _)
        (fun q a X Y hY => by
          change ((χ₁ ρ ρ₀ hρ₀ χ hχ₀ q : ZMod 3) • (a ∘ₗ ρ₀₁ ρ ρ₀ hρ₀ q⁻¹)) X =
            (χ₁ ρ ρ₀ hρ₀ χ hχ₀ q : ZMod 3) * a Y
          rw [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
          congr 2
          apply Subtype.ext
          rw [ρ₀₁_apply_coe, inv_inv, hY])
    ·
      haveI : CharP F p := (F.subtype.charP_iff_charP p).2 inferInstance
      have hp3 := p_eq_three hV ρ ρ₀ hρ₀ χ hχ₀ F g hSL hH hp2 hχ
      subst hp3
      haveI hSn : (S hV ρ F g).Normal := S_normal hV ρ F g hH
      letI : Fintype (Q ρ ⧸ S hV ρ F g) := Fintype.ofFinite _
      have hidx := not_dvd_index hV ρ F g hSL hH hp2
      refine groupCohomology.subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index
        (A := M₁ ρ ρ₀ hρ₀ χ hχ₀) (S := S hV ρ F g) ?_ ?_
      · rw [← Nat.card_eq_fintype_card]
        exact isUnit_natCast_of_not_dvd hp hidx
      · exact groupCohomology.subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map
          F (basis hV) g ((ρ₁ ρ).comp (S hV ρ F g).subtype)
          ((ρ₁_injective ρ).comp Subtype.val_injective)
          (fun s => by
            obtain ⟨m, hm⟩ := s.2
            exact ⟨m, by rw [MonoidHom.comp_apply, Subgroup.subtype_apply, ← ρGL_coe, ← hm, ψ_coe]⟩)
          (fun m => ⟨⟨θ hV ρ F g hSL m, θ_mem_S hV ρ F g hSL m⟩, by
            rw [MonoidHom.comp_apply, Subgroup.subtype_apply, ← ρGL_coe, ρGL_θ, ψ_coe]⟩)
          (Rep.res (S hV ρ F g).subtype (M₁ ρ ρ₀ hρ₀ χ hχ₀)) (LinearEquiv.refl _ _)
          (fun s a X Y hY => by
            change ((χ₁ ρ ρ₀ hρ₀ χ hχ₀ (s : Q ρ) : ZMod 3)) •
              (a ∘ₗ ρ₀₁ ρ ρ₀ hρ₀ (s : Q ρ)⁻¹) X = a Y
            rw [χ₁_eq_one_of_mem_S hV ρ ρ₀ hρ₀ χ hχ₀ F g hSL s.2, Units.val_one, one_smul,
              LinearMap.comp_apply]
            congr 1
            apply Subtype.ext
            rw [ρ₀₁_apply_coe, inv_inv, hY]
            rfl)
  ·
    letI : Fintype (Q ρ) := Fintype.ofFinite _
    apply groupCohomology.subsingleton_H1_of_isUnit_card
    rw [← Nat.card_eq_fintype_card]
    exact isUnit_natCast_of_not_dvd hp hdvd

end P2mH1piV
p2m_reactivate "P2MW.S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range.P2mH1piV"

open P2mH1piV in
theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
    {G : Type} [Group G] (ρ : G →* Module.End k V) (hfin : (Set.range ρ).Finite)
    (χ : G →* (ZMod p)ˣ) (hχ : Function.Surjective χ)
    (hirr : ∀ W : Submodule k V,
      (∀ g : G, χ g = 1 → ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k V))]
    (ρ₀ : Representation (ZMod p) G (LinearMap.ker (LinearMap.trace k V)))
    (hρ₀ : ∀ (g : G) (f : LinearMap.ker (LinearMap.trace k V)),
      ((ρ₀ g f : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) = ρ g * f * ρ g⁻¹)
    (hχ₀ : ∀ g : G, ρ₀ g = 1 → χ g = 1)
    (c : cocycles₁ ((Rep.of ρ₀).dualTwist χ))
    (hc : ∀ g : G, ρ₀ g = 1 → c g = 0) :
    H1π ((Rep.of ρ₀).dualTwist χ) c = 0 :=
  main p hp2 hV ρ hfin χ hχ hirr ρ₀ hρ₀ hχ₀ c hc

end S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range
end P2MW
export P2MW.S_groupCohomology_H1pi_dualTwist_adjointTraceZero_eq_zero_of_finite_range (solution)
