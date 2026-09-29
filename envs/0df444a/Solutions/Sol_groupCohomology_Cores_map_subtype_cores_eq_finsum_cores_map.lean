-- Prove2me | solution 1 for groupCohomology.Cores.map_subtype_cores_eq_finsum_cores_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7479d106-d4cc-526c-a9e2-e8d7cc101366

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import Theorems.Thm_groupCohomology_Cores_cores_eq_cores
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map.groupCohomology"
open scoped Pointwise

namespace groupCohomology
p2m_export "groupCohomology" "H2π congr H2π_comp_map_apply map mapCocycles₂ H2_induction_on Cores.Transversal Cores.cores Cores.cores_H2π Cores.cores_eq_cores"
namespace Cores
p2m_export "groupCohomology.Cores" "Transversal Transversal.qinv Transversal.coe_lam fintypeQuot cor₂ cor₂_apply corCocycles₂ cores cores_H2π cores_eq_cores"
p2m_open "groupCohomology.Cores groupCohomology"

attribute [local instance] fintypeQuot

namespace Mackey

open scoped Pointwise

section combinatorics

variable {G : Type} [Group G] (H D : Subgroup G) {ι : Type} (g : ι → G)

abbrev K (i : ι) : Subgroup D := (MulAut.conj (g i) • H).subgroupOf D

lemma mem_K_iff (i : ι) (x : D) : x ∈ K H D g i ↔ (g i)⁻¹ * (x : G) * g i ∈ H := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]

lemma mk_mul_eq_mk_of_mem (i : ι) (d k : D) (hk : k ∈ K H D g i) :
    (((d * k : D) : G) * g i : G ⧸ H) = ((d : G) * g i : G ⧸ H) := by
  rw [QuotientGroup.eq, Subgroup.coe_mul]
  have : ((d : G) * k * g i)⁻¹ * ((d : G) * g i) = ((g i)⁻¹ * (k : G) * g i)⁻¹ := by group
  rw [this]
  exact H.inv_mem ((mem_K_iff H D g i k).1 hk)

variable (τD : ∀ i, Transversal (K H D g i))

lemma mk_σ_mul (i : ι) (d : D) :
    ((((τD i).σ (d : D ⧸ K H D g i) : D) : G) * g i : G ⧸ H) = ((d : G) * g i : G ⧸ H) := by
  have h := (τD i).mk_σ (d : D ⧸ K H D g i)
  rw [QuotientGroup.eq] at h
  have h' : d⁻¹ * (τD i).σ (d : D ⧸ K H D g i) ∈ K H D g i := by
    have := Subgroup.inv_mem _ h
    rwa [mul_inv_rev, inv_inv] at this
  have : (τD i).σ (d : D ⧸ K H D g i) = d * (d⁻¹ * (τD i).σ (d : D ⧸ K H D g i)) := by group
  rw [this]
  exact mk_mul_eq_mk_of_mem H D g i d _ h'

def e : (Σ i, D ⧸ K H D g i) → G ⧸ H := fun x => ((((τD x.1).σ x.2 : D) : G) * g x.1 : G ⧸ H)

lemma e_apply (i : ι) (p : D ⧸ K H D g i) : e H D g τD ⟨i, p⟩ = ((((τD i).σ p : D) : G) * g i : G ⧸ H) := rfl

lemma e_mk (i : ι) (d : D) : e H D g τD ⟨i, (d : D ⧸ K H D g i)⟩ = ((d : G) * g i : G ⧸ H) := mk_σ_mul H D g τD i d

variable (hg : Function.Bijective fun i => DoubleCoset.mk D H (g i))
include hg

lemma e_surjective : Function.Surjective (e H D g τD) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨i, hi⟩ := hg.2 (DoubleCoset.mk D H x)
    obtain ⟨d, hd, h, hh, hx⟩ := (DoubleCoset.eq D H (g i) x).1 hi
    refine ⟨⟨i, ((⟨d, hd⟩ : D) : D ⧸ K H D g i)⟩, ?_⟩
    rw [e_mk, hx, QuotientGroup.eq]
    change (d * g i)⁻¹ * (d * g i * h) ∈ H
    convert hh using 1
    group

lemma e_injective : Function.Injective (e H D g τD) := by
  rintro ⟨i, p⟩ ⟨j, p'⟩ h
  rw [e_apply, e_apply, QuotientGroup.eq] at h

  obtain rfl : i = j := by
    apply hg.1
    change DoubleCoset.mk D H (g i) = DoubleCoset.mk D H (g j)
    rw [DoubleCoset.eq]
    refine ⟨(((τD j).σ p' : D) : G)⁻¹ * (((τD i).σ p : D) : G), ?_, _, h, by group⟩
    exact D.mul_mem (D.inv_mem ((τD j).σ p').2) ((τD i).σ p).2

  have hk : ((τD i).σ p)⁻¹ * (τD i).σ p' ∈ K H D g i := by
    rw [mem_K_iff]
    have : (g i)⁻¹ * (((((τD i).σ p)⁻¹ * (τD i).σ p' : D)) : G) * g i
        = ((((τD i).σ p : D) : G) * g i)⁻¹ * ((((τD i).σ p' : D) : G) * g i) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]; exact h
  have hp : p = p' := by
    rw [← (τD i).mk_σ p, ← (τD i).mk_σ p', QuotientGroup.eq]
    exact hk
  subst hp
  rfl

noncomputable def eqv : (Σ i, D ⧸ K H D g i) ≃ G ⧸ H :=
  Equiv.ofBijective (e H D g τD) ⟨e_injective H D g τD hg, e_surjective H D g τD hg⟩

lemma eqv_apply (x : Σ i, D ⧸ K H D g i) : eqv H D g τD hg x = e H D g τD x := rfl

lemma eqv_symm_mk (i : ι) (d : D) : (eqv H D g τD hg).symm ((d : G) * g i : G ⧸ H) = ⟨i, (d : D ⧸ K H D g i)⟩ := by
  rw [Equiv.symm_apply_eq, eqv_apply, e_mk]

variable (hone : ∃ i₀, g i₀ = 1)
include hone

noncomputable def adapted : Transversal H where
  σ q := (((τD ((eqv H D g τD hg).symm q).1).σ ((eqv H D g τD hg).symm q).2 : D) : G) * g ((eqv H D g τD hg).symm q).1
  mk_σ q := by
    change e H D g τD ((eqv H D g τD hg).symm q) = q
    exact (eqv H D g τD hg).apply_symm_apply q
  σ_one := by
    obtain ⟨i₀, hi₀⟩ := hone
    have h1 : (eqv H D g τD hg).symm ((1 : G) : G ⧸ H) = ⟨i₀, ((1 : D) : D ⧸ K H D g i₀)⟩ := by
      rw [← eqv_symm_mk H D g τD hg i₀ 1, Subgroup.coe_one, one_mul, hi₀]
    rw [h1]
    change (((τD i₀).σ ((1 : D) : D ⧸ K H D g i₀) : D) : G) * g i₀ = 1
    rw [(τD i₀).σ_one, Subgroup.coe_one, hi₀, one_mul]

lemma adapted_σ_mk (i : ι) (d : D) :
    (adapted H D g τD hg hone).σ ((d : G) * g i : G ⧸ H) = (((τD i).σ (d : D ⧸ K H D g i) : D) : G) * g i := by
  change (((τD ((eqv H D g τD hg).symm _).1).σ ((eqv H D g τD hg).symm _).2 : D) : G) * g ((eqv H D g τD hg).symm _).1 = _
  rw [eqv_symm_mk H D g τD hg i d]

lemma coe_lam_adapted (i : ι) (y : D) :
    ((adapted H D g τD hg hone).lam ((g i)⁻¹ * (y : G)) : G) = (g i)⁻¹ * ((((τD i).lam y : K H D g i) : D) : G) * g i := by
  rw [Transversal.coe_lam, Transversal.coe_lam, Transversal.qinv, Transversal.qinv]
  have hq : (((g i)⁻¹ * (y : G))⁻¹ : G) = ((y⁻¹ : D) : G) * g i := by rw [mul_inv_rev, inv_inv, Subgroup.coe_inv]
  rw [hq, adapted_σ_mk H D g τD hg hone i y⁻¹, Subgroup.coe_mul]
  group

end combinatorics

end Mackey
end groupCohomology.Cores

namespace groupCohomology
p2m_export "groupCohomology" "H2π congr H2π_comp_map_apply map mapCocycles₂ H2_induction_on Cores.Transversal Cores.cores Cores.cores_H2π Cores.cores_eq_cores"
namespace Cores
p2m_export "groupCohomology.Cores" "Transversal Transversal.qinv Transversal.coe_lam fintypeQuot cor₂ cor₂_apply corCocycles₂ cores cores_H2π cores_eq_cores"
p2m_open "groupCohomology.Cores groupCohomology"
namespace Mackey

attribute [local instance] fintypeQuot
open scoped Pointwise

section transfer

variable {k G : Type} [CommRing k] [Group G] [Finite G] (A : Rep.{0} k G) (H D : Subgroup G) {ι : Type} [Fintype ι] (g : ι → G)
  (τD : ∀ i, Transversal (K H D g i))
  (hg : Function.Bijective fun i => DoubleCoset.mk D H (g i)) (hone : ∃ i₀, g i₀ = 1)
  (c : ∀ i, ↥(K H D g i) →* ↥H) (hc : ∀ i (x : ↥(K H D g i)), ((c i x : ↥H) : G) = (g i)⁻¹ * ((x : ↥D) : G) * g i)

def uconj (u : H × H → A) (i : ι) : K H D g i × K H D g i → A := fun x => A.ρ (g i) (u (c i x.1, c i x.2))

omit [Finite G] [Fintype ι] in
lemma uconj_apply (u : H × H → A) (i : ι) (x₁ x₂ : K H D g i) : uconj A H D g c u i (x₁, x₂) = A.ρ (g i) (u (c i x₁, c i x₂)) := rfl

omit [Finite G] [Fintype ι] in
include hc in
lemma lam_adapted_eq (i : ι) (y : D) : (adapted H D g τD hg hone).lam ((g i)⁻¹ * (y : G)) = c i ((τD i).lam y) :=
  Subtype.ext (by rw [coe_lam_adapted, hc])

omit [Finite G] [Fintype ι] in
include hc in

lemma term_eq (u : H × H → A) (i : ι) (p : D ⧸ K H D g i) (d₁ d₂ : D) :
    A.ρ ((adapted H D g τD hg hone).σ (e H D g τD ⟨i, p⟩))
      (u ((adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ (e H D g τD ⟨i, p⟩))⁻¹ * (d₁ : G)),
        ((adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ (e H D g τD ⟨i, p⟩))⁻¹ * (d₁ : G)))⁻¹ *
          (adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ (e H D g τD ⟨i, p⟩))⁻¹ * (d₁ : G) * (d₂ : G))))
    = (Rep.res D.subtype A).ρ ((τD i).σ p)
        (uconj A H D g c u i ((τD i).lam (((τD i).σ p)⁻¹ * d₁),
          ((τD i).lam (((τD i).σ p)⁻¹ * d₁))⁻¹ * (τD i).lam (((τD i).σ p)⁻¹ * d₁ * d₂))) := by
  have hσ : (adapted H D g τD hg hone).σ (e H D g τD ⟨i, p⟩) = (((τD i).σ p : D) : G) * g i := by
    rw [e_apply, adapted_σ_mk, (τD i).mk_σ]
  have h1 : ((((τD i).σ p : D) : G) * g i)⁻¹ * (d₁ : G) = (g i)⁻¹ * ((((τD i).σ p)⁻¹ * d₁ : D) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have h2 : ((((τD i).σ p : D) : G) * g i)⁻¹ * (d₁ : G) * (d₂ : G) = (g i)⁻¹ * ((((τD i).σ p)⁻¹ * d₁ * d₂ : D) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [hσ, h2, h1, lam_adapted_eq H D g τD hg hone c hc, lam_adapted_eq H D g τD hg hone c hc, ← map_inv, ← map_mul,
    map_mul, Module.End.mul_apply]
  rfl

include hc in

theorem cor₂_adapted (u : H × H → A) (d₁ d₂ : D) :
    cor₂ A (adapted H D g τD hg hone) u ((d₁ : G), (d₂ : G)) =
      ∑ i, cor₂ (Rep.res D.subtype A) (τD i) (uconj A H D g c u i) (d₁, d₂) := by
  rw [cor₂_apply]
  have step1 :
      ∑ q : G ⧸ H, A.ρ ((adapted H D g τD hg hone).σ q)
          (u ((adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ q)⁻¹ * (d₁ : G)),
            ((adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ q)⁻¹ * (d₁ : G)))⁻¹ *
              (adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ q)⁻¹ * (d₁ : G) * (d₂ : G))))
        = ∑ x : (Σ i, D ⧸ K H D g i), A.ρ ((adapted H D g τD hg hone).σ (e H D g τD x))
          (u ((adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ (e H D g τD x))⁻¹ * (d₁ : G)),
            ((adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ (e H D g τD x))⁻¹ * (d₁ : G)))⁻¹ *
              (adapted H D g τD hg hone).lam (((adapted H D g τD hg hone).σ (e H D g τD x))⁻¹ * (d₁ : G) * (d₂ : G)))) :=
    (Fintype.sum_equiv (eqv H D g τD hg) _ _ (fun _ => rfl)).symm
  rw [step1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cor₂_apply]
  exact Finset.sum_congr rfl fun p _ => term_eq A H D g τD hg hone c hc u i p d₁ d₂

end transfer

end Mackey
end groupCohomology.Cores

namespace groupCohomology
p2m_export "groupCohomology" "H2π congr H2π_comp_map_apply map mapCocycles₂ H2_induction_on Cores.Transversal Cores.cores Cores.cores_H2π Cores.cores_eq_cores"
namespace Cores
p2m_export "groupCohomology.Cores" "Transversal Transversal.qinv Transversal.coe_lam fintypeQuot cor₂ cor₂_apply corCocycles₂ cores cores_H2π cores_eq_cores"
p2m_open "groupCohomology.Cores groupCohomology"
namespace Mackey

attribute [local instance] fintypeQuot
open scoped Pointwise

section classes

variable {k G : Type} [CommRing k] [Group G] [Finite G] (A : Rep.{0} k G) (H D : Subgroup G) {ι : Type} [Fintype ι] (g : ι → G)
  (τD : ∀ i, Transversal (K H D g i))
  (hg : Function.Bijective fun i => DoubleCoset.mk D H (g i)) (hone : ∃ i₀, g i₀ = 1)
  (c : ∀ i, ↥(K H D g i) →* ↥H) (hc : ∀ i (x : ↥(K H D g i)), ((c i x : ↥H) : G) = (g i)⁻¹ * ((x : ↥D) : G) * g i)
  (T : ∀ i, Rep.res (c i) (Rep.res H.subtype A) ⟶ Rep.res (K H D g i).subtype (Rep.res D.subtype A))
  (hT : ∀ i (a : A), (T i).hom a = A.ρ (g i) a)

include hg hone hc hT in
theorem mackey (τ : Transversal H) (y : groupCohomology (Rep.res H.subtype A) 2) :
    (groupCohomology.map D.subtype (𝟙 (Rep.res D.subtype A)) 2).hom (Cores.cores A τ y) =
      ∑ i, Cores.cores (Rep.res D.subtype A) (τD i) ((groupCohomology.map (c i) (T i) 2).hom y) := by
  induction y using H2_induction_on with
  | h u =>
    rw [Cores.cores_eq_cores A H τ (adapted H D g τD hg hone), Cores.cores_H2π, groupCohomology.H2π_comp_map_apply]
    have hterm : ∀ i, Cores.cores (Rep.res D.subtype A) (τD i) ((groupCohomology.map (c i) (T i) 2).hom (H2π (Rep.res H.subtype A) u))
        = H2π (Rep.res D.subtype A) (corCocycles₂ (Rep.res D.subtype A) (τD i) (mapCocycles₂ (c i) (T i) u)) := fun i => by
      rw [groupCohomology.H2π_comp_map_apply, Cores.cores_H2π]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← map_sum]
    congr 1
    apply Subtype.ext
    funext dd
    obtain ⟨d₁, d₂⟩ := dd
    change cor₂ A (adapted H D g τD hg hone) u ((d₁ : G), (d₂ : G)) = _
    rw [cor₂_adapted A H D g τD hg hone c hc u d₁ d₂]
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = cor₂ (Rep.res D.subtype A) (τD i) (⇑(mapCocycles₂ (c i) (T i) u)) (d₁, d₂)
    congr 1
    funext x
    obtain ⟨x₁, x₂⟩ := x
    rw [uconj_apply]
    exact (hT i _).symm

end classes

end Mackey
end groupCohomology.Cores

theorem solution
    {k G : Type} [CommRing k] [Group G] [Finite G] (A : Rep.{0} k G)
    (H D : Subgroup G) (τ : Cores.Transversal H)

    {ι : Type} [Finite ι] (g : ι → G)
    (hg : Function.Bijective fun i => DoubleCoset.mk D H (g i))
    (hone : ∃ i₀, g i₀ = 1)

    (τD : ∀ i, Cores.Transversal ((MulAut.conj (g i) • H).subgroupOf D))
    (c : ∀ i, ↥((MulAut.conj (g i) • H).subgroupOf D) →* ↥H)
    (hc : ∀ i (x : ↥((MulAut.conj (g i) • H).subgroupOf D)), ((c i x : ↥H) : G) = (g i)⁻¹ * ((x : ↥D) : G) * g i)
    (T : ∀ i, Rep.res (c i) (Rep.res H.subtype A) ⟶ Rep.res ((MulAut.conj (g i) • H).subgroupOf D).subtype (Rep.res D.subtype A))
    (hT : ∀ i (a : A), (T i).hom a = A.ρ (g i) a)
    (y : groupCohomology (Rep.res H.subtype A) 2) :
    (groupCohomology.map D.subtype (𝟙 (Rep.res D.subtype A)) 2).hom (Cores.cores A τ y) =
      ∑ᶠ i, Cores.cores (Rep.res D.subtype A) (τD i) ((groupCohomology.map (c i) (T i) 2).hom y) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  exact groupCohomology.Cores.Mackey.mackey A H D g τD hg hone c hc T hT τ y

end S_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map
end P2MW
export P2MW.S_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map (solution)
