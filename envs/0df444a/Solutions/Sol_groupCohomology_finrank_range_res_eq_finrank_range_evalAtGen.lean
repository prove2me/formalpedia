-- Prove2me | solution 1 for groupCohomology.finrank_range_res_eq_finrank_range_evalAtGen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e7746c8c-2483-5bf5-a346-8a47b0ac2548

import Mathlib
import Definitions.Def_GroupCohomology_TateTwist
import Theorems.Thm_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen

open CategoryTheory Module groupCohomology

universe u

set_option autoImplicit false

namespace Ws14Port
namespace groupCohomology

open _root_.groupCohomology
open Rep (res)

section Conjugation

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

private noncomputable def pSum' (A : Rep k G) (g : G) (m : ℕ) : Module.End k A :=
  ∑ i ∈ Finset.range m, A.ρ (g ^ i)

private lemma pSum'_apply (g : G) (m : ℕ) (x : A) :
    pSum' A g m x = ∑ i ∈ Finset.range m, A.ρ (g ^ i) x :=
  LinearMap.sum_apply _ _ _

private lemma pSum'_succ_apply (g : G) (m : ℕ) (x : A) :
    pSum' A g (m + 1) x = A.ρ (g ^ m) x + pSum' A g m x := by
  simp only [pSum'_apply, Finset.sum_range_succ]
  exact add_comm _ _

private lemma cocycles₁_apply_pow' (f : cocycles₁ A) (g : G) (m : ℕ) :
    f (g ^ m) = pSum' A g m (f g) := by
  induction m with
  | zero =>
      rw [pow_zero, pSum', Finset.range_zero, Finset.sum_empty]
      exact cocycles₁_map_one f
  | succ m ih =>
      rw [pow_succ, (mem_cocycles₁_iff (⇑f)).1 f.2 (g ^ m) g, ih, pSum'_succ_apply]

lemma rho_pow_sub_one_apply_mem (t : G) (j : ℕ) (x : A) :
    A.ρ (t ^ j) x - x ∈ LinearMap.range (A.ρ t - 1) := by
  refine ⟨pSum' A t j x, ?_⟩
  have h : (A.ρ t - 1) * pSum' A t j = A.ρ (t ^ j) - 1 := by
    rw [map_pow, ← mul_geom_sum (A.ρ t) j]
    congr 1
    exact Finset.sum_congr rfl fun i _ => map_pow _ _ _
  calc (A.ρ t - 1) (pSum' A t j x) = ((A.ρ t - 1) * pSum' A t j) x := rfl
    _ = (A.ρ (t ^ j) - 1) x := by rw [h]
    _ = A.ρ (t ^ j) x - x := rfl

private lemma pSum'_rho_sub_one_apply (t : G) (j : ℕ) (y : A) :
    pSum' A t j (A.ρ t y - y) = A.ρ (t ^ j) y - y := by
  have h : pSum' A t j * (A.ρ t - 1) = A.ρ (t ^ j) - 1 := by
    rw [map_pow, ← geom_sum_mul (A.ρ t) j]
    congr 1
    exact Finset.sum_congr rfl fun i _ => map_pow _ _ _
  calc pSum' A t j (A.ρ t y - y) = (pSum' A t j * (A.ρ t - 1)) y := rfl
    _ = (A.ρ (t ^ j) - 1) y := by rw [h]
    _ = A.ρ (t ^ j) y - y := rfl

lemma pSum_sub_nsmul_mem (t : G) (m : ℕ) (x : A) :
    pSum' A t m x - m • x ∈ LinearMap.range (A.ρ t - 1) := by
  induction m with
  | zero => simp [pSum'_apply]
  | succ m ih =>
      have h : pSum' A t (m + 1) x - (m + 1) • x =
          (pSum' A t m x - m • x) + (A.ρ (t ^ m) x - x) := by
        rw [pSum'_succ_apply, succ_nsmul]
        abel
      rw [h]
      exact Submodule.add_mem _ ih (rho_pow_sub_one_apply_mem t m x)

lemma cocycles₁_apply_conj (f : cocycles₁ A) (g s : G) :
    A.ρ g (f (g⁻¹ * s * g)) = f s + (A.ρ s (f g) - f g) := by
  have h1 : f (s * g) = A.ρ s (f g) + f s := (mem_cocycles₁_iff (⇑f)).1 f.2 s g
  have h2 : f (g * (g⁻¹ * s * g)) = A.ρ g (f (g⁻¹ * s * g)) + f g :=
    (mem_cocycles₁_iff (⇑f)).1 f.2 g (g⁻¹ * s * g)
  have h3 : g * (g⁻¹ * s * g) = s * g := by group
  rw [h3, h1] at h2
  rw [eq_sub_of_add_eq h2.symm]
  abel

lemma range_rho_sub_one_le_comap [Finite G] (t g : G)
    (h : g * t * g⁻¹ ∈ Subgroup.zpowers t) :
    LinearMap.range (A.ρ t - 1) ≤ (LinearMap.range (A.ρ t - 1)).comap (A.ρ g) := by
  obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers.2 h
  replace hj : t ^ j = g * t * g⁻¹ := hj
  have hgt : g * t = t ^ j * g := by rw [hj]; group
  rintro _ ⟨x, rfl⟩
  simp only [Submodule.mem_comap]
  have key : A.ρ g ((A.ρ t - 1) x) = A.ρ (t ^ j) (A.ρ g x) - A.ρ g x := by
    have e1 : A.ρ g (A.ρ t x) = A.ρ (t ^ j) (A.ρ g x) := by
      rw [← Module.End.mul_apply, ← map_mul, hgt, map_mul, Module.End.mul_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, e1]
  rw [key]
  exact rho_pow_sub_one_apply_mem t j (A.ρ g x)

end Conjugation

section TateOperator

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

variable {A} in

lemma nsmul_rho_apply_sub_apply_mem [Finite G] (f : cocycles₁ A) {t φ : G} {m : ℕ}
    (hm : φ⁻¹ * t * φ = t ^ m) (hst : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) :
    m • A.ρ φ (f t) - f t ∈ LinearMap.range (A.ρ t - 1) := by

  have hconj : A.ρ φ (f (t ^ m)) - f t ∈ LinearMap.range (A.ρ t - 1) := by
    rw [← hm, cocycles₁_apply_conj f φ t]
    exact ⟨f φ, by simp⟩

  have htel : A.ρ φ (f (t ^ m)) - m • A.ρ φ (f t) ∈ LinearMap.range (A.ρ t - 1) := by
    have h1 : A.ρ φ (f (t ^ m)) - m • A.ρ φ (f t) =
        A.ρ φ (pSum' A t m (f t) - m • f t) := by
      rw [map_sub, map_nsmul, cocycles₁_apply_pow']
    rw [h1]
    exact range_rho_sub_one_le_comap t φ hst (pSum_sub_nsmul_mem t m (f t))

  have h2 : m • A.ρ φ (f t) - f t =
      (A.ρ φ (f (t ^ m)) - f t) - (A.ρ φ (f (t ^ m)) - m • A.ρ φ (f t)) := by abel
  rw [h2]
  exact Submodule.sub_mem _ hconj htel

lemma range_evalAtGen_le_ker [Finite G] (t φ : G) (m : ℕ)
    (hm : φ⁻¹ * t * φ = t ^ m) (hst : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) :
    LinearMap.range (evalAtGen A t) ≤
      LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1) := by
  rintro _ ⟨f, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    evalAtGen_apply]
  calc (m • frobeniusOnCoinvariants A t φ hst) (Submodule.Quotient.mk (f t))
      = m • (frobeniusOnCoinvariants A t φ hst) (Submodule.Quotient.mk (f t)) :=
        LinearMap.smul_apply m _ _
    _ = m • (Submodule.Quotient.mk (A.ρ φ (f t)) : A ⧸ LinearMap.range (A.ρ t - 1)) := rfl
    _ = Submodule.Quotient.mk (m • A.ρ φ (f t)) :=
        (map_nsmul ((LinearMap.range (A.ρ t - 1)).mkQ) m (A.ρ φ (f t))).symm
    _ = Submodule.Quotient.mk (f t) :=
        (Submodule.Quotient.eq _).2 (nsmul_rho_apply_sub_apply_mem f hm hst)

end TateOperator

section KernelIdentification

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

lemma res_H1π_eq_zero_iff [Finite G] (S : Subgroup G) [S.Normal] (t : G) (ht : t ∈ S)
    (htS : S ≤ Subgroup.zpowers t) (f : cocycles₁ A) :
    ModuleCat.Hom.hom (H1InfRes A S).g (ModuleCat.Hom.hom (H1π A) f) = 0 ↔
      (f : G → A) t ∈ LinearMap.range (A.ρ t - 1) := by
  have hcomm : ModuleCat.Hom.hom ((H1InfRes A S).g) (ModuleCat.Hom.hom (H1π A) f) =
      H1π (res S.subtype A) (mapCocycles₁ S.subtype (𝟙 _) f) :=
    H1π_comp_map_apply S.subtype (𝟙 _) f
  rw [hcomm]
  refine Iff.trans (H1π_eq_zero_iff _) ?_
  constructor
  ·
    rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [d₀₁_hom_apply, coe_mapCocycles₁ (x := f)] using congr_fun hy ⟨t, ht⟩
  ·
    rintro ⟨y, hy⟩
    have hyt : A.ρ t y - y = f t := hy
    refine ⟨y, funext fun s => ?_⟩
    obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers.2 (htS s.2)
    replace hj : t ^ j = (s : G) := hj
    have h2 : f ((s : G)) = A.ρ (s : G) y - y := by
      rw [← hj, cocycles₁_apply_pow' f t j, ← hyt, pSum'_rho_sub_one_apply]
    simpa [d₀₁_hom_apply, coe_mapCocycles₁ (x := f)] using h2.symm

lemma ker_res_comp_H1π [Finite G] (S : Subgroup G) [S.Normal] (t : G) (ht : t ∈ S)
    (htS : S ≤ Subgroup.zpowers t) :
    LinearMap.ker (ModuleCat.Hom.hom (H1InfRes A S).g ∘ₗ ModuleCat.Hom.hom (H1π A)) =
      LinearMap.ker (evalAtGen A t) := by
  ext f
  exact (res_H1π_eq_zero_iff A S t ht htS f).trans
    (Submodule.Quotient.mk_eq_zero (LinearMap.range (A.ρ t - 1))).symm

end KernelIdentification

section FromTameDevissage

section Finiteness
variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

scoped instance [Finite G] [FiniteDimensional k A] : FiniteDimensional k (cocycles₁ A) := by
  have : FiniteDimensional k (G → A) := Module.Finite.pi
  exact FiniteDimensional.finiteDimensional_submodule (cocycles₁ A)

scoped instance [Finite G] [FiniteDimensional k A] : FiniteDimensional k (H1 A) :=
  Module.Finite.of_surjective (ModuleCat.Hom.hom (H1π A))
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
end Finiteness

def invariantsQuotientToInvariantsEquiv' {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    (A.quotientToInvariants S).ρ.invariants ≃ₗ[k] A.ρ.invariants where
  toFun x := ⟨x.1.1, fun g => congrArg Subtype.val (x.2 (QuotientGroup.mk g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨y.1, fun s => y.2 s.1⟩, fun q => QuotientGroup.induction_on q
    fun g => Subtype.ext (y.2 g)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := rfl

theorem finrank_H1_eq_finrank_range_inf_add_finrank_range_res {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    {k : Type u} [Field k] (A : Rep k G) [FiniteDimensional k (groupCohomology.H1 A)] :
    finrank k (groupCohomology.H1 A) = finrank k (LinearMap.range (ModuleCat.Hom.hom (groupCohomology.H1InfRes A S).f)) +
      finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) := by
  have hexact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (H1InfRes_exact A S)
  haveI : FiniteDimensional k ((H1InfRes A S).X₂ : Type u) := ‹FiniteDimensional k (H1 A)›
  have h := LinearMap.finrank_range_add_finrank_ker (ModuleCat.Hom.hom (H1InfRes A S).g)
  rw [← hexact, add_comm] at h
  exact h.symm

theorem finrank_range_inf_eq_finrank_invariants {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    {k : Type u} [Field k] (A : Rep k G) [Finite G] [Fintype (G ⧸ S)]
    [FiniteDimensional k A]
    {φ : G} (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (hN : (A.quotientToInvariants S).ρ.norm = 0) :
    finrank k (LinearMap.range (ModuleCat.Hom.hom (groupCohomology.H1InfRes A S).f)) = finrank k A.ρ.invariants := by
  haveI hfd : FiniteDimensional k (A.quotientToInvariants S) :=
    inferInstanceAs (FiniteDimensional k (Representation.invariants (A.ρ.comp S.subtype)))
  have e : finrank k (LinearMap.range (ModuleCat.Hom.hom (groupCohomology.H1InfRes A S).f)) = finrank k (groupCohomology.H1 (A.quotientToInvariants S)) :=
    LinearMap.finrank_range_of_inj ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (H1InfRes A S).f))
  rw [e, _root_.groupCohomology.finrank_H1_eq_finrank_invariants_of_norm_eq_zero (A.quotientToInvariants S) hφ hN,
    (invariantsQuotientToInvariantsEquiv' A S).finrank_eq]

end FromTameDevissage

section DimensionCount

variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

lemma finrank_range_res_eq_finrank_range_evalAtGen [Finite G] [FiniteDimensional k A]
    (S : Subgroup G) [S.Normal] (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t) :
    finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) =
      finrank k (LinearMap.range (evalAtGen A t)) := by

  have hsurj : LinearMap.range (ModuleCat.Hom.hom (H1π A)) = ⊤ :=
    LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have h3 : LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g ∘ₗ
      ModuleCat.Hom.hom (H1π A)) = LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g) :=
    LinearMap.range_comp_of_range_eq_top _ hsurj

  have h4 := LinearMap.finrank_range_add_finrank_ker
    (ModuleCat.Hom.hom (H1InfRes A S).g ∘ₗ ModuleCat.Hom.hom (H1π A))
  have h5 := LinearMap.finrank_range_add_finrank_ker (evalAtGen A t)
  have h6 : finrank k (LinearMap.ker (ModuleCat.Hom.hom (H1InfRes A S).g ∘ₗ
      ModuleCat.Hom.hom (H1π A))) = finrank k (LinearMap.ker (evalAtGen A t)) := by
    rw [ker_res_comp_H1π A S t ht htS]

  have h7 : finrank k (ModuleCat.of k (cocycles₁ A) : Type u) = finrank k (cocycles₁ A) := rfl
  rw [← h3]
  omega

theorem finrank_H1_le_finrank_invariants_add_finrank_ker
    [Finite G] [FiniteDimensional k A] (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]
    (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t)
    {φ : G} (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (hN : (A.quotientToInvariants S).ρ.norm = 0)
    (m : ℕ) (hm : φ⁻¹ * t * φ = t ^ m)
    (hst : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) :
    finrank k (H1 A) ≤ finrank k A.ρ.invariants +
      finrank k (LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1)) := by

  have h1 := finrank_H1_eq_finrank_range_inf_add_finrank_range_res S A
  have h2 := finrank_range_inf_eq_finrank_invariants S A hφ hN
  rw [h1, h2]

  have h3 := finrank_range_res_eq_finrank_range_evalAtGen A S t ht htS
  have h4 : finrank k (LinearMap.range (evalAtGen A t)) ≤
      finrank k (LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1)) :=
    Submodule.finrank_mono (range_evalAtGen_le_ker A t φ m hm hst)
  omega

end DimensionCount

end Ws14Port.groupCohomology
p2m_reactivate "P2MW.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen.Ws14Port P2MW.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen.Ws14Port.groupCohomology"
p2m_reactivate "P2MW.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen.Ws14Port"

theorem solution {k G : Type u} [Field k] [Group G] (A : Rep k G) [Finite G] [FiniteDimensional k A]
    (S : Subgroup G) [S.Normal] (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t) :
    finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) =
      finrank k (LinearMap.range (groupCohomology.evalAtGen A t)) := by
  exact Ws14Port.groupCohomology.finrank_range_res_eq_finrank_range_evalAtGen A S t ht htS

end S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen
end P2MW
export P2MW.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen (solution)
