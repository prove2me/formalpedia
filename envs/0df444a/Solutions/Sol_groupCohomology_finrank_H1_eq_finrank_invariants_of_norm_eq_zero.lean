-- Prove2me | solution 1 for groupCohomology.finrank_H1_eq_finrank_invariants_of_norm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/99cab1ee-539e-597a-b951-4f35ea798b73

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero

universe u

namespace W2TD
open groupCohomology
open CategoryTheory Finset Module

namespace groupCohomology

section Cyclic

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

private noncomputable def pSum (A : Rep k G) (g : G) (m : ℕ) : Module.End k A :=
  ∑ i ∈ Finset.range m, A.ρ (g ^ i)

private lemma pSum_apply (g : G) (m : ℕ) (x : A) :
    pSum A g m x = ∑ i ∈ Finset.range m, A.ρ (g ^ i) x :=
  LinearMap.sum_apply _ _ _

private lemma pSum_zero_apply (g : G) (x : A) : pSum A g 0 x = 0 := by
  simp [pSum_apply]

private lemma pSum_one_apply (g : G) (x : A) : pSum A g 1 x = x := by
  simp [pSum_apply]

private lemma pSum_succ_apply (g : G) (m : ℕ) (x : A) :
    pSum A g (m + 1) x = A.ρ (g ^ m) x + pSum A g m x := by
  simp only [pSum_apply, Finset.sum_range_succ]
  exact add_comm _ _

private lemma pSum_add_apply (g : G) (m n : ℕ) (x : A) :
    pSum A g (m + n) x = pSum A g m x + A.ρ (g ^ m) (pSum A g n x) := by
  simp only [pSum_apply, Finset.sum_range_add, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [pow_add, map_mul, Module.End.mul_apply]

private lemma exists_pow_eq [Finite G] {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (q : G) :
    ∃ m : ℕ, g ^ m = q :=
  (isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.2 (hg q)

private lemma cocycles₁_apply_pow (f : cocycles₁ A) (g : G) (m : ℕ) :
    f (g ^ m) = pSum A g m (f g) := by
  induction m with
  | zero => rw [pow_zero, pSum_zero_apply]; exact cocycles₁_map_one f
  | succ m ih =>
      rw [pow_succ, (mem_cocycles₁_iff (⇑f)).1 f.2 (g ^ m) g, ih, pSum_succ_apply]

variable [Fintype G]

private lemma pSum_card_apply (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : A) :
    pSum A g (Fintype.card G) x = A.ρ.norm x := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  rw [pSum_apply, Representation.norm, LinearMap.sum_apply]
  refine Finset.sum_bij (fun i _ => g ^ i) (fun i _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa [hord] using Finset.mem_range.1 hi)
      (by simpa [hord] using Finset.mem_range.1 hj) hij
  · intro y _
    obtain ⟨m, hm⟩ := exists_pow_eq hg y
    refine ⟨m % Fintype.card G, Finset.mem_range.2 (Nat.mod_lt _ Fintype.card_pos), ?_⟩
    show g ^ (m % Fintype.card G) = y
    rw [← hord, pow_mod_orderOf]
    exact hm
  · exact fun i _ => rfl

variable (A) in

lemma norm_cocycles₁_apply_self {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (f : cocycles₁ A) : A.ρ.norm (f g) = 0 := by
  rw [← pSum_card_apply g hg, ← cocycles₁_apply_pow f g, pow_card_eq_one]
  exact cocycles₁_map_one f

private lemma pSum_card_mul_apply (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : A}
    (hx : A.ρ.norm x = 0) (j : ℕ) : pSum A g (Fintype.card G * j) x = 0 := by
  induction j with
  | zero => exact pSum_zero_apply g x
  | succ j ih =>
      rw [Nat.mul_succ, pSum_add_apply, ih, zero_add, pSum_card_apply g hg, hx, map_zero]

private lemma pSum_apply_eq_of_pow_eq (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : A}
    (hx : A.ρ.norm x = 0) {m m' : ℕ} (h : g ^ m = g ^ m') :
    pSum A g m x = pSum A g m' x := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have key : ∀ l : ℕ, pSum A g l x = pSum A g (l % Fintype.card G) x := by
    intro l
    conv_lhs => rw [← Nat.mod_add_div l (Fintype.card G)]
    rw [pSum_add_apply, pSum_card_mul_apply g hg hx, map_zero, add_zero]
  have hmod : m % Fintype.card G = m' % Fintype.card G := by
    rw [← hord]; exact pow_inj_mod.1 h
  rw [key m, key m', hmod]

private noncomputable def cocycleOfKerNorm (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x : A) (hx : A.ρ.norm x = 0) : cocycles₁ A := by
  refine ⟨fun q => pSum A g (exists_pow_eq hg q).choose x, (mem_cocycles₁_iff _).2
    fun q₁ q₂ => ?_⟩
  have h12 : g ^ ((exists_pow_eq hg q₁).choose + (exists_pow_eq hg q₂).choose) = q₁ * q₂ := by
    rw [pow_add, (exists_pow_eq hg q₁).choose_spec, (exists_pow_eq hg q₂).choose_spec]
  rw [pSum_apply_eq_of_pow_eq g hg hx ((exists_pow_eq hg (q₁ * q₂)).choose_spec.trans
    h12.symm), pSum_add_apply, (exists_pow_eq hg q₁).choose_spec, add_comm]

private lemma cocycleOfKerNorm_apply (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (x : A) (hx : A.ρ.norm x = 0) {m : ℕ} {q : G} (hq : g ^ m = q) :
    cocycleOfKerNorm g hg x hx q = pSum A g m x :=
  pSum_apply_eq_of_pow_eq g hg hx ((exists_pow_eq hg q).choose_spec.trans hq.symm)

variable (A) in

noncomputable def cocycles₁EquivKerNorm {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    cocycles₁ A ≃ₗ[k] LinearMap.ker A.ρ.norm where
  toFun f := ⟨f g, norm_cocycles₁_apply_self A hg f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := cocycleOfKerNorm g hg x.1 x.2
  left_inv f := by
    ext q
    obtain ⟨m, hm⟩ := exists_pow_eq hg q
    rw [cocycleOfKerNorm_apply g hg _ _ hm, ← cocycles₁_apply_pow f g m, hm]
  right_inv x := Subtype.ext <|
    (cocycleOfKerNorm_apply g hg x.1 x.2 (pow_one g)).trans (pSum_one_apply g x.1)

variable (A) in

lemma finrank_cocycles₁_of_forall_mem_zpowers {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    finrank k (cocycles₁ A) = finrank k (LinearMap.ker A.ρ.norm) :=
  (cocycles₁EquivKerNorm A hg).finrank_eq

end Cyclic

section DimensionCount

variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

lemma finrank_coboundaries₁_add_finrank_invariants [FiniteDimensional k A] :
    finrank k (coboundaries₁ A) + finrank k A.ρ.invariants = finrank k A := by
  rw [coboundaries₁, ← d₀₁_ker_eq_invariants]
  exact LinearMap.finrank_range_add_finrank_ker (d₀₁ A).hom

scoped instance [Finite G] [FiniteDimensional k A] : FiniteDimensional k (cocycles₁ A) := by
  have : FiniteDimensional k (G → A) := Module.Finite.pi
  exact FiniteDimensional.finiteDimensional_submodule (cocycles₁ A)

scoped instance [Finite G] [FiniteDimensional k A] : FiniteDimensional k (H1 A) :=
  Module.Finite.of_surjective (ModuleCat.Hom.hom (H1π A))
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

lemma finrank_H1_add_finrank_coboundaries₁ [Finite G] [FiniteDimensional k A] :
    finrank k (H1 A) + finrank k (coboundaries₁ A) = finrank k (cocycles₁ A) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (ModuleCat.Hom.hom (H1π A))
  rw [LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance),
    finrank_top] at h1
  have hker : LinearMap.ker (ModuleCat.Hom.hom (H1π A)) =
      Submodule.comap (cocycles₁ A).subtype (coboundaries₁ A) := by
    ext f
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact H1π_eq_zero_iff f
  rw [hker, (Submodule.comapSubtypeEquivOfLe (coboundaries₁_le_cocycles₁ A)).finrank_eq] at h1
  exact h1

theorem finrank_H1_add_finrank_range_norm [Fintype G] [FiniteDimensional k A]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    finrank k (H1 A) + finrank k (LinearMap.range A.ρ.norm) = finrank k A.ρ.invariants := by
  have h1 := finrank_H1_add_finrank_coboundaries₁ A
  have h2 := finrank_coboundaries₁_add_finrank_invariants A
  have h3 := finrank_cocycles₁_of_forall_mem_zpowers A hg
  have h4 := LinearMap.finrank_range_add_finrank_ker A.ρ.norm
  omega

theorem finrank_H1_eq_finrank_invariants_of_norm_eq_zero [Fintype G] [FiniteDimensional k A]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (hN : A.ρ.norm = 0) :
    finrank k (H1 A) = finrank k A.ρ.invariants := by
  have h := finrank_H1_add_finrank_range_norm A hg
  rw [hN, LinearMap.range_zero, finrank_bot] at h
  omega

end DimensionCount

end groupCohomology
p2m_reactivate "P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD.groupCohomology"
end W2TD
p2m_reactivate "P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD.groupCohomology P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD"

namespace W2LB
open groupCohomology
open CategoryTheory Module

namespace groupCohomology

section CyclicEngine

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

theorem normHomCompSub_trivial_g_eq_zero (V : Type u) [AddCommGroup V] [Module k V] (g : G) :
    (Rep.FiniteCyclicGroup.normHomCompSub (Rep.trivial k G V) g).g = 0 := by
  ext v
  simp [Rep.sub_hom, Rep.applyAsHom]

theorem normHomCompSub_trivial_f_eq_zero (V : Type u) [AddCommGroup V] [Module k V] (g : G)
    (hcard : (Fintype.card G : k) = 0) :
    (Rep.FiniteCyclicGroup.normHomCompSub (Rep.trivial k G V) g).f = 0 := by
  have key : ∀ v : V, (Rep.trivial k G V).ρ.norm v = 0 := by
    intro v
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, hcard, zero_smul]
  ext v
  have h__af := key v
  simp at h__af
  exact h__af

noncomputable def H2TrivialIso (V : Type u) [AddCommGroup V] [Module k V]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (hcard : (Fintype.card G : k) = 0) :
    H2 (Rep.trivial k G V) ≅ ModuleCat.of k V :=
  Rep.FiniteCyclicGroup.groupCohomologyIsoEven (Rep.trivial k G V) g hg 2 even_two ≪≫
    (ShortComplex.HomologyData.ofZeros _
      (normHomCompSub_trivial_f_eq_zero V g hcard)
      (normHomCompSub_trivial_g_eq_zero V g)).left.homologyIso

theorem finrank_H2_trivial_eq_finrank {k G : Type u} [Field k] [CommGroup G] [Fintype G]
    (V : Type u) [AddCommGroup V] [Module k V]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (hcard : (Fintype.card G : k) = 0) :
    finrank k (H2 (Rep.trivial k G V)) = finrank k V :=
  (H2TrivialIso V g hg hcard).toLinearEquiv.finrank_eq

end CyclicEngine
p2m_reactivate "P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD.groupCohomology P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD"

end groupCohomology
p2m_reactivate "P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD.groupCohomology P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD"
end W2LB
p2m_reactivate "P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD.groupCohomology P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero.W2TD"

open CategoryTheory Module groupCohomology

theorem solution
    {k G : Type u} [Field k] [Group G] (A : Rep k G) [Fintype G] [FiniteDimensional k A]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (hN : A.ρ.norm = 0) :
    finrank k (groupCohomology.H1 A) = finrank k A.ρ.invariants :=
  W2TD.groupCohomology.finrank_H1_eq_finrank_invariants_of_norm_eq_zero A hg hN

end S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero
end P2MW
export P2MW.S_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero (solution)
