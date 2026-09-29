-- Prove2me | solution 1 for groupCohomology.theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9baca43a-fe72-5c9c-998d-6d7c1a5b92ec

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_Rep_dualTwist_cycloChar_smooth
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Theorems.Thm_groupCohomology_exists_eq_d12_of_invariant_of_mul_dvd_orderOf
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Theorems.Thm_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
open scoped Pointwise

universe u

section Normalise

variable {k G : Type} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

private theorem isLevelConstant₁_coboundary (A : Rep k G) (m : A)
    (hm : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → A.ρ s m = m) :
    IsLevelConstant₁ r (fun s : G => A.ρ s m - m) := by
  obtain ⟨F, hF, h⟩ := hm
  refine ⟨F, hF, fun g s hs => ?_⟩
  simp only [map_mul, Module.End.mul_apply, h s hs]

private theorem exists_cocycle_eq_zero_on (A : Rep k G) (P : G → Prop) (c : cocycles₁ A)
    (hc : IsLevelConstant₁ r (⇑c)) (m : A)
    (hm : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → A.ρ s m = m)
    (hP : ∀ s, P s → c s = A.ρ s m - m) :
    ∃ c₀ : cocycles₁ A, IsLevelConstant₁ r (⇑c₀) ∧ (∀ s, P s → c₀ s = 0) ∧ H1π A c₀ = H1π A c := by
  have hb : (fun s : G => A.ρ s m - m) ∈ coboundaries₁ A := ⟨m, rfl⟩
  set δ : cocycles₁ A := ⟨fun s => A.ρ s m - m, coboundaries₁_le_cocycles₁ A hb⟩ with hδ
  refine ⟨c - δ, ?_, ?_, ?_⟩
  · have h1 : IsLevelConstant₁ r (Neg.neg ∘ fun s : G => A.ρ s m - m) :=
      (isLevelConstant₁_coboundary r A m hm).comp Neg.neg
    convert hc.add h1 using 2
    ext s
    show c s - (A.ρ s m - m) = c s + -(A.ρ s m - m)
    rw [sub_eq_add_neg]
  · intro s hs
    show c s - (A.ρ s m - m) = 0
    rw [hP s hs, sub_self]
  · rw [H1π_eq_iff]
    convert (coboundaries₁ A).neg_mem hb using 1
    ext s
    show c s - (A.ρ s m - m) - c s = -(A.ρ s m - m)
    rw [sub_sub_cancel_left]

end Normalise

section Local

variable {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]

private def Inert (s : primeLocalGaloisGroup q) : Prop :=
  primeLocalToGlobal q s ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ

section Vanishing

variable {k G : Type} [CommRing k] [Group G]

private theorem coc_mul {A : Rep k G} (f : cocycles₁ A) (a b : G) :
    f (a * b) = A.ρ a (f b) + f a :=
  (mem_cocycles₁_iff (A := A) (⇑f)).1 f.2 a b

private def zeroSubgroup {A : Rep k G} (f : cocycles₁ A) : Subgroup G where
  carrier := {s | f s = 0}
  one_mem' := cocycles₁_map_one f
  mul_mem' := by
    intro a b ha hb
    have ha' : f a = 0 := ha
    have hb' : f b = 0 := hb
    show f (a * b) = 0
    rw [coc_mul, ha', hb', map_zero, add_zero]
  inv_mem' := by
    intro a ha
    have ha' : f a = 0 := ha
    show f a⁻¹ = 0
    have h := coc_mul f a⁻¹ a
    rw [inv_mul_cancel, cocycles₁_map_one, ha', map_zero, zero_add] at h
    exact h.symm

private theorem eq_zero_of_mem_sup {A : Rep k G} (f : cocycles₁ A) (H K : Subgroup G)
    (hH : ∀ s ∈ H, f s = 0) (hK : ∀ s ∈ K, f s = 0) : ∀ s ∈ H ⊔ K, f s = 0 := by
  intro s hs
  have hHz : H ≤ zeroSubgroup f := fun x hx => hH x hx
  have hKz : K ≤ zeroSubgroup f := fun x hx => hK x hx
  exact (sup_le hHz hKz) hs

private theorem ρ_apply_eq_of_forall_eq_zero {A : Rep k G} (f : cocycles₁ A) (N : Subgroup G) [N.Normal]
    (h0 : ∀ s ∈ N, f s = 0) {n : G} (hn : n ∈ N) (s : G) : A.ρ n (f s) = f s := by
  have hmem : s⁻¹ * n * s ∈ N := by
    simpa using (Subgroup.Normal.conj_mem inferInstance n hn s⁻¹)
  have h1 : f (n * s) = A.ρ n (f s) := by rw [coc_mul, h0 n hn, add_zero]
  have h2 : f (n * s) = f s := by
    calc f (n * s) = f (s * (s⁻¹ * n * s)) := by congr 1; group
      _ = A.ρ s (f (s⁻¹ * n * s)) + f s := coc_mul f s _
      _ = f s := by rw [h0 _ hmem, map_zero, zero_add]
  rw [← h1, h2]

end Vanishing

section Cup

variable {k G : Type} [CommRing k] [Group G] {A B N : Rep k G}
  (φ : A →ₗ[k] B →ₗ[k] N) (f : cocycles₁ A) (g : cocycles₁ B)

private theorem cupCochain_mul_right_fst {n : G} (hfn : f n = 0) (hgn : ∀ t, B.ρ n (g t) = g t)
    (s t : G) : cupCochain φ (⇑f) (⇑g) (s * n, t) = cupCochain φ (⇑f) (⇑g) (s, t) := by
  rw [cupCochain_apply, cupCochain_apply, coc_mul f s n, hfn, map_zero, zero_add, map_mul,
    Module.End.mul_apply, hgn t]

private theorem cupCochain_mul_right_snd {n : G} (hgn : g n = 0) (s t : G) :
    cupCochain φ (⇑f) (⇑g) (s, t * n) = cupCochain φ (⇑f) (⇑g) (s, t) := by
  rw [cupCochain_apply, cupCochain_apply, coc_mul g t n, hgn, map_zero, zero_add]

private theorem ρ_cupCochain_eq (hφ : Rep.IsEquivariantBilinear A B N φ) (N₀ : Subgroup G) [N₀.Normal]
    (hf0 : ∀ s ∈ N₀, f s = 0) (hg0 : ∀ s ∈ N₀, g s = 0) {n : G} (hn : n ∈ N₀) (st : G × G) :
    N.ρ n (cupCochain φ (⇑f) (⇑g) st) = cupCochain φ (⇑f) (⇑g) st := by
  have hφ' : ∀ (x : G) (a : A) (b : B), φ (A.ρ x a) (B.ρ x b) = N.ρ x (φ a b) := hφ
  obtain ⟨s, t⟩ := st
  have hmem : s⁻¹ * n * s ∈ N₀ := by
    simpa using (Subgroup.Normal.conj_mem inferInstance n hn s⁻¹)
  have hB : B.ρ n (B.ρ s (g t)) = B.ρ s (g t) := by
    rw [← Module.End.mul_apply, ← map_mul, show n * s = s * (s⁻¹ * n * s) by group, map_mul,
      Module.End.mul_apply, ρ_apply_eq_of_forall_eq_zero g N₀ hg0 hmem t]
  rw [cupCochain_apply, ← hφ' n, ρ_apply_eq_of_forall_eq_zero f N₀ hf0 hn s, hB]

private theorem cupCochain_mem_cocycles₂ (hφ : Rep.IsEquivariantBilinear A B N φ) :
    cupCochain φ (⇑f) (⇑g) ∈ cocycles₂ N := by
  have h := (cup φ hφ f g).2
  rwa [cocycles₂.val_eq_coe, cup_coe] at h

end Cup

section Coboundary

variable {k G : Type} [CommRing k] [Group G]

private theorem isOfFinOrder_mk_of_exists (N' : Subgroup G) [N'.Normal] (φF : G)
    (h : ∃ n : ℕ, (φF ^ n)⁻¹ * φF⁻¹ ∈ N') : IsOfFinOrder (QuotientGroup.mk φF : G ⧸ N') := by
  obtain ⟨n, hn⟩ := h
  have hpow : φF ^ (n + 1) ∈ N' := by
    have h' := N'.inv_mem hn
    rwa [mul_inv_rev, inv_inv, inv_inv, ← pow_succ'] at h'
  exact isOfFinOrder_iff_pow_eq_one.2
    ⟨n + 1, n.succ_pos, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hpow⟩

private theorem pow_orderOf_mk_mem (N' : Subgroup G) [N'.Normal] (φF : G) :
    φF ^ orderOf (QuotientGroup.mk φF : G ⧸ N') ∈ N' := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_orderOf_eq_one _

private theorem comap_fixingSubgroup_le (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {E E' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hEE' : E ≤ E') :
    (E'.fixingSubgroup).comap r ≤ (E.fixingSubgroup).comap r := by
  intro u hu
  rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
  exact fun x hx => hu x (hEE' hx)

private theorem fixingSubgroup_normalClosure_normal (E : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    (IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)).fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker]
  infer_instance

private theorem eq_zero_of_mem_comap_fixingSubgroup
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A : Rep k G} (f : cocycles₁ A)
    {E : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hE : ∀ g s : G, r s ∈ E.fixingSubgroup → f (g * s) = f g) :
    ∀ u ∈ (E.fixingSubgroup).comap r, f u = 0 := by
  intro u hu
  have h := hE 1 u hu
  rwa [one_mul, cocycles₁_map_one] at h

private theorem cupCochain_mem_levelCocycles₂_and_levelCoboundaries₂
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {A B : Rep k G} {N : Rep.{0} k G} (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (I : Subgroup G) [I.Normal] (φF : G)
    (hgen : ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : G),
      ∃ n : ℕ, (φF ^ n)⁻¹ * g ∈ I ⊔ (F.fixingSubgroup).comap r)
    (hdiv : ∀ (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀] (n : ℕ), 0 < n →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧
        ∀ j : ℕ, φF ^ j ∈ I ⊔ (F.fixingSubgroup).comap r → n ∣ j)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hℓN : ∀ x : N, ℓ • x = 0)
    (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f)) (hfI : ∀ s ∈ I, f s = 0)
    (g : cocycles₁ B) (hg : IsLevelConstant₁ r (⇑g)) (hgI : ∀ s ∈ I, g s = 0) :
    cupCochain φ (⇑f) (⇑g) ∈ levelCocycles₂ r N ∧ cupCochain φ (⇑f) (⇑g) ∈ levelCoboundaries₂ r N := by
  obtain ⟨Ff, hFf, hf'⟩ := hf
  obtain ⟨Fg, hFg, hg'⟩ := hg
  haveI := hFf
  haveI := hFg

  let F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥(Ff ⊔ Fg)) (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F₀ := normalClosure.is_finiteDimensional ℚ (↥(Ff ⊔ Fg)) (AlgebraicClosure ℚ)
  haveI hF₀n : F₀.fixingSubgroup.Normal := fixingSubgroup_normalClosure_normal _
  have hFfF₀ : Ff ≤ F₀ := le_sup_left.trans (IntermediateField.le_normalClosure (Ff ⊔ Fg))
  have hFgF₀ : Fg ≤ F₀ := le_sup_right.trans (IntermediateField.le_normalClosure (Ff ⊔ Fg))
  let N₀ : Subgroup G := I ⊔ (F₀.fixingSubgroup).comap r
  haveI : N₀.Normal := Subgroup.sup_normal _ _
  have hf0 : ∀ s ∈ N₀, f s = 0 :=
    eq_zero_of_mem_sup f _ _ hfI fun u hu =>
      eq_zero_of_mem_comap_fixingSubgroup r f hf' u (comap_fixingSubgroup_le r hFfF₀ hu)
  have hg0 : ∀ s ∈ N₀, g s = 0 :=
    eq_zero_of_mem_sup g _ _ hgI fun u hu =>
      eq_zero_of_mem_comap_fixingSubgroup r g hg' u (comap_fixingSubgroup_le r hFgF₀ hu)
  set E : G × G → N := cupCochain φ (⇑f) (⇑g) with hEdef
  have hE₁ : ∀ (s t : G) {n : G}, n ∈ N₀ → E (s * n, t) = E (s, t) := fun s t n hn =>
    cupCochain_mul_right_fst φ f g (hf0 n hn) (fun t' => ρ_apply_eq_of_forall_eq_zero g N₀ hg0 hn t') s t
  have hE₂ : ∀ (s t : G) {n : G}, n ∈ N₀ → E (s, t * n) = E (s, t) := fun s t n hn =>
    cupCochain_mul_right_snd φ f g (hg0 n hn) s t
  have hEcoc : E ∈ cocycles₂ N := cupCochain_mem_cocycles₂ φ f g hφ
  have hElevel : IsLevelConstant₂ r E :=
    ⟨F₀, inferInstance, fun s t u u' hu hu' =>
      (hE₂ (s * u) t (Subgroup.mem_sup_right (Subgroup.mem_comap.2 hu'))).trans
        (hE₁ s t (Subgroup.mem_sup_right (Subgroup.mem_comap.2 hu)))⟩
  refine ⟨(mem_levelCocycles₂_iff r N E).2 ⟨hEcoc, hElevel⟩, ?_⟩

  have hfin₀ : IsOfFinOrder (QuotientGroup.mk φF : G ⧸ N₀) :=
    isOfFinOrder_mk_of_exists N₀ φF (hgen F₀ φF⁻¹)
  set e : ℕ := orderOf (QuotientGroup.mk φF : G ⧸ N₀) with he_def
  have he : 0 < e := hfin₀.orderOf_pos
  have hφe : φF ^ e ∈ N₀ := pow_orderOf_mk_mem N₀ φF

  obtain ⟨F, hF₀F, hFfin, hFdiv⟩ := hdiv F₀ (ℓ * e) (Nat.mul_pos hℓ he)
  haveI := hFfin
  let F' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥F) (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F' := normalClosure.is_finiteDimensional ℚ (↥F) (AlgebraicClosure ℚ)
  haveI hF'n : F'.fixingSubgroup.Normal := fixingSubgroup_normalClosure_normal _
  have hFF' : F ≤ F' := IntermediateField.le_normalClosure F
  let N' : Subgroup G := I ⊔ (F'.fixingSubgroup).comap r
  haveI : N'.Normal := Subgroup.sup_normal _ _
  have hN'N₀ : N' ≤ N₀ := sup_le_sup_left (comap_fixingSubgroup_le r (hF₀F.trans hFF')) I
  have hN'F : N' ≤ I ⊔ (F.fixingSubgroup).comap r := sup_le_sup_left (comap_fixingSubgroup_le r hFF') I
  have hgen' : ∀ x : G, ∃ n : ℕ, (φF ^ n)⁻¹ * x ∈ N' := fun x => hgen F' x
  have hfin' : IsOfFinOrder (QuotientGroup.mk φF : G ⧸ N') := isOfFinOrder_mk_of_exists N' φF (hgen F' φF⁻¹)
  have hdiv' : ℓ * e ∣ orderOf (QuotientGroup.mk φF : G ⧸ N') :=
    hFdiv _ (hN'F (pow_orderOf_mk_mem N' φF))

  let W : Subrepresentation N.ρ :=
    { toSubmodule := Representation.invariants (N.ρ.comp N₀.subtype)
      apply_mem_toSubmodule := by
        intro x v hv
        rw [Representation.mem_invariants] at hv ⊢
        rintro ⟨n, hn⟩
        have hmem : x⁻¹ * n * x ∈ N₀ := by
          simpa using (Subgroup.Normal.conj_mem inferInstance n hn x⁻¹)
        show N.ρ n (N.ρ x v) = N.ρ x v
        rw [← Module.End.mul_apply, ← map_mul, show n * x = x * (x⁻¹ * n * x) by group, map_mul,
          Module.End.mul_apply]
        congr 1
        exact hv ⟨_, hmem⟩ }
  let Arep : Rep k G := Rep.of W.toRepresentation
  have hℓA : ∀ a : Arep, ℓ • a = 0 := fun a => Subtype.ext (by
    show ℓ • (a : N) = 0
    exact hℓN _)
  have hN : ∀ n ∈ N', Arep.ρ n = 1 := by
    intro n hn
    refine LinearMap.ext fun a => Subtype.ext ?_
    show N.ρ n (a : N) = (a : N)
    exact (Representation.mem_invariants _ _).1 a.2 ⟨n, hN'N₀ hn⟩
  let E' : G × G → Arep := fun st =>
    ⟨E st, (Representation.mem_invariants _ _).2 fun n => ρ_cupCochain_eq φ f g hφ N₀ hf0 hg0 n.2 st⟩
  have hE'coc : E' ∈ cocycles₂ Arep := by
    rw [mem_cocycles₂_iff]
    intro a b c
    have h := (mem_cocycles₂_iff (A := N) E).1 hEcoc a b c
    exact Subtype.ext h
  have hE'e : ∀ x y : G, E' (x * φF ^ e, y) = E' (x, y) := by
    intro x y
    apply Subtype.ext
    exact hE₁ x y hφe
  have hE'₁ : ∀ x y n : G, n ∈ N' → E' (x * n, y) = E' (x, y) := by
    intro x y n hn
    apply Subtype.ext
    exact hE₁ x y (hN'N₀ hn)
  have hE'₂ : ∀ x y n : G, n ∈ N' → E' (x, y * n) = E' (x, y) := by
    intro x y n hn
    apply Subtype.ext
    exact hE₂ x y (hN'N₀ hn)
  obtain ⟨bW, hbN, hbE⟩ := exists_eq_d12_of_invariant_of_mul_dvd_orderOf Arep ℓ hℓA N' hN φF hgen' hfin' e
    hdiv' E' hE'coc hE'e hE'₁ hE'₂
  rw [mem_levelCoboundaries₂_iff]
  refine ⟨fun s => (bW s : N), ⟨F', inferInstance, fun x u hu => ?_⟩, ?_⟩
  · show (bW (x * u) : N) = (bW x : N)
    rw [hbN x u (Subgroup.mem_sup_right (Subgroup.mem_comap.2 hu))]
  · funext st
    obtain ⟨x, y⟩ := st
    have h := congrArg Subtype.val (hbE x y)
    simp only [d₁₂_hom_apply]
    exact h.symm

end Coboundary

private theorem inertiaComap_normal :
    (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).Normal := by
  refine ⟨fun n hn x => ?_⟩
  rw [Subgroup.mem_comap] at hn ⊢
  rw [map_mul, map_mul, map_inv]
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hstab : primeLocalToGlobal q x ∈ (primeLocalPlace q).decompositionSubgroup ℚ :=
    localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) x
  have hfix : (primeLocalToGlobal q x)⁻¹ • primeLocalPlace q = primeLocalPlace q :=
    MulAction.mem_stabilizer_iff.1 (Subgroup.inv_mem _ hstab)
  have hσ : primeLocalToGlobal q n ∈ ((primeLocalToGlobal q x)⁻¹ • primeLocalPlace q).inertiaSubgroupIn ℚ := by
    rw [hfix]; exact hn
  have h := ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul (primeLocalPlace q)
    (primeLocalToGlobal q x)⁻¹ hσ
  rwa [inv_inv] at h

omit [FiniteDimensional (ZMod p) M] in

private theorem exists_levelCocycle_inv_eq_zero
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q)
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (c₀ : cocycles₁ (Rep.res (primeLocalToGlobal q) M)) (hc₀ : IsLevelConstant₁ (primeLocalToGlobal q) (⇑c₀))
    (hc₀I : ∀ s, Inert q s → c₀ s = 0)
    (c₀' : cocycles₁ (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))))
    (hc₀' : IsLevelConstant₁ (primeLocalToGlobal q) (⇑c₀')) (hc₀'I : ∀ s, Inert q s → c₀' s = 0) :
    ∃ e : ↥(levelCocycles₂ (primeLocalToGlobal q)
        (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))),
      (∀ st, (e : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
          ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) st
        = cupCochain (Module.Dual.eval (ZMod p) M :
            Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p]
              Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
                ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) (⇑c₀) (⇑c₀') st) ∧
      inv (continuousH2π _ _ e) = 0 := by
  have _ := hsm
  let I : Subgroup (primeLocalGaloisGroup q) :=
    ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
  haveI : I.Normal := inertiaComap_normal q
  obtain ⟨φF, hφF⟩ := exists_isFrobeniusAt_apply_primeLocalToGlobal q
  have hφ : Rep.IsEquivariantBilinear (Rep.res (primeLocalToGlobal q) M)
      (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
      (Module.Dual.eval (ZMod p) M) := by
    intro s a b
    show ((cycloChar p (primeLocalToGlobal q s) : ZMod p) • (b ∘ₗ M.ρ (primeLocalToGlobal q s)⁻¹))
        (M.ρ (primeLocalToGlobal q s) a)
      = (cycloChar p (primeLocalToGlobal q s) : ZMod p) • b a
    rw [LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  have hℓN : ∀ x : ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)), p • x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  obtain ⟨hcoc, hcob⟩ := cupCochain_mem_levelCocycles₂_and_levelCoboundaries₂ (primeLocalToGlobal q)
    (Module.Dual.eval (ZMod p) M) hφ I φF
    (fun F _ x => exists_frobenius_pow_inv_mul_mem_inertia_sup_level q φF hφF F x)
    (fun F₀ _ n hn => exists_level_dvd_of_frobenius_pow_mem_inertia_sup q φF hφF F₀ n hn)
    p (Fact.out : p.Prime).pos hℓN c₀ hc₀ (fun s hs => hc₀I s hs) c₀' hc₀' (fun s hs => hc₀'I s hs)
  refine ⟨⟨_, hcoc⟩, fun _ => rfl, ?_⟩
  rw [(continuousH2π_eq_zero_iff _ _ ⟨_, hcoc⟩).2 hcob, map_zero]

end Local

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q)
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (θ₁ : continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))))
    (hθ₁ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M :
        Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p] Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
          ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
      inv θ₁)
    (Lur : Submodule (ZMod p) (H1 (Rep.res (primeLocalToGlobal q) M)))
    (hLur : ∀ x : H1 (Rep.res (primeLocalToGlobal q) M), x ∈ Lur ↔
      ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal q) M),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M, ∀ s, primeLocalToGlobal q s ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ →
          c.val s = (Rep.res (primeLocalToGlobal q) M).ρ s m - m) ∧
        H1π _ c = x)
    (L'ur : Submodule (ZMod p) (H1 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))))
    (hL'ur : ∀ x : H1 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))), x ∈ L'ur ↔
      ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ g s, primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
        (∃ m : M.dualTwist (cycloChar p),
          ∀ s, primeLocalToGlobal q s ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ →
            c.val s = (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))).ρ s m - m) ∧
        H1π _ c = x)
    (x : continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) (hx : (x : H1 (Rep.res (primeLocalToGlobal q) M)) ∈ Lur)
    (y : continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))))
    (hy : (y : H1 (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)))) ∈ L'ur) :
    θ₁ x y = 0 := by

  obtain ⟨c, hc, ⟨m, hm⟩, hcx⟩ := (hLur _).1 hx
  obtain ⟨c', hc', ⟨m', hm'⟩, hc'y⟩ := (hL'ur _).1 hy
  have hmsm : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → (Rep.res (primeLocalToGlobal q) M).ρ s m = m := by
    obtain ⟨F, hF, h⟩ := hsm m
    exact ⟨F, hF, fun s hs => h _ hs⟩
  have hm'sm : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup →
        (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))).ρ s m' = m' := by
    obtain ⟨F, hF, h⟩ := Rep.dualTwist_cycloChar_smooth M hsm m'
    exact ⟨F, hF, fun s hs => h _ hs⟩
  obtain ⟨c₀, hc₀, hc₀I, hc₀c⟩ :=
    exists_cocycle_eq_zero_on (primeLocalToGlobal q) _ (Inert q) c hc m hmsm hm
  obtain ⟨c₀', hc₀', hc₀'I, hc₀'c'⟩ :=
    exists_cocycle_eq_zero_on (primeLocalToGlobal q) _ (Inert q) c' hc' m' hm'sm hm'

  obtain ⟨e, he, hinv⟩ : ∃ e : ↥(levelCocycles₂ (primeLocalToGlobal q)
        (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))),
      (∀ st, (e : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
          ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) st
        = cupCochain (Module.Dual.eval (ZMod p) M :
            Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p]
              Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
                ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) (⇑c₀) (⇑c₀') st) ∧
      inv (continuousH2π _ _ e) = 0 := by
    exact exists_levelCocycle_inv_eq_zero q M hsm inv c₀ hc₀ hc₀I c₀' hc₀' hc₀'I

  have hx' : x = ⟨(H1π _).hom c₀, H1π_mem_continuousH1 _ _ hc₀⟩ := by
    apply Subtype.ext
    show (x : H1 _) = H1π _ c₀
    rw [hc₀c, hcx]
  have hy' : y = ⟨(H1π _).hom c₀', H1π_mem_continuousH1 _ _ hc₀'⟩ := by
    apply Subtype.ext
    show (y : H1 _) = H1π _ c₀'
    rw [hc₀'c', hc'y]
  rw [hx', hy', hθ₁ c₀ hc₀ c₀' hc₀' e he, hinv]

end S_groupCohomology_theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified
end P2MW
export P2MW.S_groupCohomology_theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified (solution)
