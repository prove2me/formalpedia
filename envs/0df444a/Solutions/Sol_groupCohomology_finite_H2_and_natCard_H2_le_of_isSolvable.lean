-- Prove2me | solution 1 for groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b601fc9a-0167-5062-b7d7-61cdbac7f23c

import Mathlib
import Theorems.Thm_groupCohomology_finite_H2_and_natCard_H2_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "H2 d₁₂_hom_apply map H2_induction_on H2π_eq_zero_iff H1 finite_H2_and_natCard_H2_le"
namespace Br8
p2m_open "groupCohomology"

private theorem exists_normal_prime_index {H : Type} [Group H] [Finite H] [Group.IsSolvable H] [Nontrivial H] :
    ∃ N : Subgroup H, N.Normal ∧ (Nat.card (H ⧸ N)).Prime := by
  classical

  have hc : commutator H ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := H)
    have hall : ∀ m, derivedSeries H m = ⊤ := by
      intro m
      induction m with
      | zero => exact derivedSeries_zero H
      | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
    exact (bot_ne_top (α := Subgroup H)) (by rw [← hn, hall])

  let S : Set (Subgroup H) := {B | commutator H ≤ B ∧ B ≠ ⊤}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨commutator H, le_rfl, hc⟩
  obtain ⟨B, ⟨hcB, hBtop⟩, hmax'⟩ := Set.Finite.exists_maximal hSfin hSne
  have hmax : ∀ B' ∈ S, B ≤ B' → B = B' := fun B' hB' hle => le_antisymm hle (hmax' hB' hle)

  have hnormal : ∀ B' : Subgroup H, commutator H ≤ B' → B'.Normal := fun B' hB' =>
    ⟨fun b hb g => by
      have h1 : g * b * g⁻¹ * b⁻¹ ∈ B' :=
        hB' (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top b))
      have h2 : g * b * g⁻¹ * b⁻¹ * b = g * b * g⁻¹ := by group
      rw [← h2]
      exact B'.mul_mem h1 hb⟩
  haveI hBn : B.Normal := hnormal B hcB
  refine ⟨B, hBn, ?_⟩

  have hcomm : ∀ a b : H ⧸ B, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x =>
    induction b using QuotientGroup.induction_on with | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (x * y)⁻¹ * (y * x) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by group
    rw [this]
    exact hcB (Subgroup.commutator_mem_commutator (Subgroup.mem_top y⁻¹) (Subgroup.mem_top x⁻¹))
  letI : CommGroup (H ⧸ B) := { (inferInstance : Group (H ⧸ B)) with mul_comm := hcomm }

  haveI : Nontrivial (H ⧸ B) := QuotientGroup.nontrivial_iff.2 hBtop
  haveI : IsSimpleGroup (H ⧸ B) := by
    refine IsSimpleGroup.mk (fun N _ => ?_)
    let B' : Subgroup H := N.comap (QuotientGroup.mk' B)
    have hBB' : B ≤ B' := fun x hx => by
      change (QuotientGroup.mk' B x) ∈ N
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact N.one_mem
    have hN : N = B'.map (QuotientGroup.mk' B) :=
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective B) N).symm
    by_cases hB'top : B' = ⊤
    · right
      rw [hN, hB'top, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    · left
      have hB'S : B' ∈ S := ⟨hcB.trans hBB', hB'top⟩
      have hEq : B = B' := hmax B' hB'S hBB'
      rw [hN, ← hEq, QuotientGroup.map_mk'_self]
  exact IsSimpleGroup.prime_card
end groupCohomology.Br8

namespace groupCohomology
p2m_export "groupCohomology" "H2 d₁₂_hom_apply map H2_induction_on H2π_eq_zero_iff H1 finite_H2_and_natCard_H2_le"
namespace Br8
p2m_open "groupCohomology"

private theorem subsingleton_H2_of_subsingleton {H : Type} [Group H] [Subsingleton H] (B : Rep.{0} ℤ H) :
    Subsingleton (H2 B) := by
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ x : H2 B, x = 0 by rw [h a, h b]
  intro x
  induction x using H2_induction_on with | h c =>
  rw [H2π_eq_zero_iff]
  refine ⟨fun _ => c (1, 1), funext fun q => ?_⟩
  obtain ⟨g, h⟩ := q
  rw [Subsingleton.elim g 1, Subsingleton.elim h 1, d₁₂_hom_apply, MonoidHom.map_one B.ρ]
  simp

end groupCohomology.Br8

theorem solution
    {G : Type} [Group G] [Finite G] [Group.IsSolvable G] (A : Rep.{0} ℤ G)
    (h90 : ∀ (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      Subsingleton (H1 (Rep.res φ A)))
    (hcyc : ∀ (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      ∀ (N : Subgroup H) [N.Normal], (Nat.card (H ⧸ N)).Prime →
        Finite (H2 ((Rep.res φ A).quotientToInvariants N)) ∧
          Nat.card (H2 ((Rep.res φ A).quotientToInvariants N)) ≤ Nat.card (H ⧸ N)) :
    Finite (H2 A) ∧ Nat.card (H2 A) ≤ Nat.card G := by
  suffices key : ∀ (n : ℕ) (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      Nat.card H ≤ n → Finite (H2 (Rep.res φ A)) ∧ Nat.card (H2 (Rep.res φ A)) ≤ Nat.card H by
    exact key (Nat.card G) G (MonoidHom.id G) (fun _ _ h => h) le_rfl
  intro n
  induction n with
  | zero =>
    intro H _ _ φ _ hH
    exact absurd hH (not_le.2 Nat.card_pos)
  | succ n ih =>
    intro H _ _ φ hφ hH
    by_cases htriv : Subsingleton H
    · haveI := groupCohomology.Br8.subsingleton_H2_of_subsingleton (Rep.res φ A)
      refine ⟨Finite.of_subsingleton, ?_⟩
      rw [Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩]
      exact Nat.card_pos
    · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.1 htriv
      haveI : Group.IsSolvable H := solvable_of_solvable_injective hφ
      obtain ⟨N, hN, hprime⟩ := groupCohomology.Br8.exists_normal_prime_index (H := H)
      haveI := hN
      have hinjN : Function.Injective (φ.comp N.subtype) := hφ.comp N.subtype_injective
      haveI : Subsingleton (H1 (Rep.res N.subtype (Rep.res φ A))) := h90 N (φ.comp N.subtype) hinjN
      obtain ⟨hfinQ, hleQ⟩ := hcyc H φ hφ N hprime
      have hindex : Nat.card N * Nat.card (H ⧸ N) = Nat.card H := by
        rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
      have hcardN : Nat.card N ≤ n := by
        have h2 : 2 ≤ Nat.card (H ⧸ N) := hprime.two_le
        have : Nat.card N * 2 ≤ Nat.card H := by
          calc Nat.card N * 2 ≤ Nat.card N * Nat.card (H ⧸ N) := Nat.mul_le_mul_left _ h2
            _ = Nat.card H := hindex
        omega
      obtain ⟨hfinN, hleN⟩ := ih N (φ.comp N.subtype) hinjN hcardN
      haveI : Finite (H2 ((Rep.res φ A).quotientToInvariants N)) := hfinQ
      haveI : Finite (H2 (Rep.res N.subtype (Rep.res φ A))) := hfinN
      obtain ⟨hfin, hle⟩ := groupCohomology.finite_H2_and_natCard_H2_le (Rep.res φ A) N
      refine ⟨hfin, hle.trans ?_⟩
      calc Nat.card (H2 ((Rep.res φ A).quotientToInvariants N)) * Nat.card (H2 (Rep.res N.subtype (Rep.res φ A)))
          ≤ Nat.card (H ⧸ N) * Nat.card N := Nat.mul_le_mul hleQ hleN
        _ = Nat.card H := by rw [mul_comm, hindex]

end S_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable
end P2MW
export P2MW.S_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable (solution)
