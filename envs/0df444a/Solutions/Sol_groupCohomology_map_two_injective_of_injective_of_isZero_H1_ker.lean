-- Prove2me | solution 1 for groupCohomology.map_two_injective_of_injective_of_isZero_H1_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/3de157a8-2a23-5613-b3d3-54aa0eaf550c

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker

set_option autoImplicit false
open CategoryTheory

namespace groupCohomology
p2m_export "groupCohomology" "H2 H2π cocycles₂_map_one_fst coboundaries₁ H1π mem_cocycles₁_iff cocycles₂ H1π_eq_zero_iff d₁₂_hom_apply coboundaries₂ H2π_comp_map_apply map cocycles₂_map_one_snd π d₀₁_hom_apply mapCocycles₂ H2_induction_on cocycles₁ H2π_eq_zero_iff"
namespace H2InflInj
p2m_open "groupCohomology"

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G)
  (C : Rep ℤ G) (C' : Rep ℤ G') (j : Rep.res π C ⟶ C')

lemma j_comm (a : G') (c : C) : j.hom (C.ρ (π a) c) = C'.ρ a (j.hom c) :=
  Rep.hom_comm_apply j a c

lemma mapCocycles₂_apply (f : cocycles₂ C) (a b : G') :
    ((mapCocycles₂ π j).hom f) (a, b) = j.hom (f (π a, π b)) := rfl

end groupCohomology.H2InflInj

open CategoryTheory _root_.groupCohomology _root_.P2MW.S_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker.groupCohomology groupCohomology.H2InflInj in

theorem solution {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G']
    (π : G' →* G) (hπ : Function.Surjective π)
    (C : Rep ℤ G) (C' : Rep ℤ G') (j : Rep.res π C ⟶ C') (hj : Function.Injective j.hom)
    (hjN : ∀ c' : C', (∀ g' : G', g' ∈ π.ker → C'.ρ g' c' = c') → c' ∈ Set.range j.hom)
    (h1 : CategoryTheory.Limits.IsZero (groupCohomology (Rep.res π.ker.subtype C') 1)) :
    Function.Injective (groupCohomology.map π j 2).hom := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with
  | _ f =>

  have hx' : (H2π C').hom ((mapCocycles₂ π j).hom f) = 0 := by
    rw [← H2π_comp_map_apply]; exact hx
  rw [H2π_eq_zero_iff, coboundaries₂] at hx'
  obtain ⟨u, hu⟩ := hx'
  have hu' : ∀ a b : G', C'.ρ a (u b) - u (a * b) + u a = j.hom (f (π a, π b)) := fun a b => by
    have h := congrFun hu (a, b)
    rw [d₁₂_hom_apply] at h
    exact h
  set c₀ : C := f (1, 1) with hc₀

  have hjfix : ∀ n : G', n ∈ π.ker → ∀ c : C, C'.ρ n (j.hom c) = j.hom c := by
    intro n hn c
    have h := j_comm π C C' j n c
    rw [(MonoidHom.mem_ker).1 hn, MonoidHom.map_one C.ρ] at h
    exact h.symm

  have hN : ∀ n m : G', n ∈ π.ker → m ∈ π.ker → C'.ρ n (u m) - u (n * m) + u n = j.hom c₀ := by
    intro n m hn hm
    rw [hu' n m, (MonoidHom.mem_ker).1 hn, (MonoidHom.mem_ker).1 hm]
  let w : π.ker → C' := fun n => u n - j.hom c₀
  have hw : w ∈ cocycles₁ (Rep.res π.ker.subtype C') := by
    rw [mem_cocycles₁_iff]
    intro n m
    change u (n * m : G') - j.hom c₀ = C'.ρ (n : G') (u m - j.hom c₀) + (u n - j.hom c₀)
    rw [map_sub, hjfix n n.2, ← hN n m n.2 m.2]
    abel

  haveI : Subsingleton (groupCohomology (Rep.res π.ker.subtype C') 1) := ModuleCat.isZero_iff_subsingleton.mp h1
  have hw0 : (H1π (Rep.res π.ker.subtype C')).hom ⟨w, hw⟩ = 0 := Subsingleton.elim _ _
  rw [H1π_eq_zero_iff, coboundaries₁] at hw0
  obtain ⟨c₁, hc₁⟩ := hw0
  have hc₁' : ∀ n : G', n ∈ π.ker → u n - j.hom c₀ = C'.ρ n c₁ - c₁ := by
    intro n hn
    have h := congrFun hc₁ ⟨n, hn⟩
    rw [d₀₁_hom_apply] at h
    exact h.symm

  let u₂ : G' → C' := fun a => u a - (C'.ρ a c₁ - c₁)
  have hu₂ : ∀ a b : G', C'.ρ a (u₂ b) - u₂ (a * b) + u₂ a = j.hom (f (π a, π b)) := by
    intro a b
    rw [← hu' a b]
    simp only [u₂, map_sub, map_mul, Module.End.mul_apply]
    abel
  have hu₂N : ∀ n : G', n ∈ π.ker → u₂ n = j.hom c₀ := by
    intro n hn
    simp only [u₂]
    rw [← hc₁' n hn]
    abel

  have hP1 : ∀ a n : G', n ∈ π.ker → u₂ (a * n) = u₂ a := by
    intro a n hn
    have h := hu₂ a n
    rw [(MonoidHom.mem_ker).1 hn, cocycles₂_map_one_snd, j_comm, ← hc₀, ← hu₂N n hn] at h

    have := congrArg (fun z => z - C'.ρ a (u₂ n)) h
    rw [sub_self] at this
    rw [eq_comm, ← sub_eq_zero, ← this]
    abel
  have hP2 : ∀ n b : G', n ∈ π.ker → u₂ (n * b) = C'.ρ n (u₂ b) := by
    intro n b hn
    have h := hu₂ n b
    rw [(MonoidHom.mem_ker).1 hn, cocycles₂_map_one_fst, ← hc₀, ← hu₂N n hn] at h

    rw [← sub_eq_zero] at h ⊢
    rw [← neg_eq_zero, ← h]
    abel
  have hP3 : ∀ b n : G', n ∈ π.ker → C'.ρ n (u₂ b) = u₂ b := by
    intro b n hn
    have hn' : b⁻¹ * n * b ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, (MonoidHom.mem_ker).1 hn, mul_one, ← map_mul, inv_mul_cancel, map_one]
    rw [← hP2 n b hn, show n * b = b * (b⁻¹ * n * b) by group, hP1 b _ hn']

  have hrange : ∀ b : G', u₂ b ∈ Set.range j.hom := fun b => hjN _ (fun n hn => hP3 b n hn)
  choose v' hv' using hrange
  have hv'N : ∀ a n : G', n ∈ π.ker → v' (a * n) = v' a := by
    intro a n hn
    apply hj
    rw [hv', hv', hP1 a n hn]
  obtain ⟨s, hs⟩ : ∃ s : G → G', ∀ g, π (s g) = g := ⟨Function.surjInv hπ, Function.surjInv_eq hπ⟩
  let v : G → C := fun g => v' (s g)
  have hv : ∀ a : G', v (π a) = v' a := by
    intro a
    change v' (s (π a)) = v' a
    have hn : a⁻¹ * s (π a) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, hs, map_inv, inv_mul_cancel]
    rw [show s (π a) = a * (a⁻¹ * s (π a)) by group, hv'N a _ hn]

  rw [H2π_eq_zero_iff, coboundaries₂]
  refine ⟨v, funext fun gh => ?_⟩
  obtain ⟨g, h⟩ := gh
  obtain ⟨a, rfl⟩ := hπ g
  obtain ⟨b, rfl⟩ := hπ h
  rw [d₁₂_hom_apply]
  apply hj
  change j.hom (C.ρ (π a) (v (π b)) - v (π a * π b) + v (π a)) = j.hom (f (π a, π b))
  rw [← map_mul, hv, hv, hv, map_add, map_sub, j_comm, hv', hv', hv', hu₂]

end S_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker
end P2MW
export P2MW.S_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker (solution)
