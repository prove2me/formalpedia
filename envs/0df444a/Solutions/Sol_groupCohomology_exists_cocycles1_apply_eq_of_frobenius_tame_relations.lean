-- Prove2me | solution 1 for groupCohomology.exists_cocycles1_apply_eq_of_frobenius_tame_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a2f7d254-28b0-52a9-b486-370809c76bf3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_cocycles1_apply_eq_of_frobenius_tame_relations

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
    (t φ : G) (m fo jo : ℕ)
    (hm : φ⁻¹ * t * φ = t ^ m)
    (hrel : φ ^ fo = t ^ jo) (hmin : ∀ d : ℕ, φ ^ d ∈ Subgroup.zpowers t → fo ∣ d)
    (hgen : ∀ x : G, ∃ a b : ℕ, x = φ ^ a * t ^ b)
    (hNφ : ∑ i ∈ Finset.range fo, A.ρ (φ ^ i) = 0)
    (v w : A)
    (hNe : ∑ i ∈ Finset.range (orderOf t), A.ρ (t ^ i) v = 0)
    (hNj : ∑ i ∈ Finset.range jo, A.ρ (t ^ i) v = 0)
    (hw : A.ρ t w - w = A.ρ φ (∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - v) :
    ∃ c : cocycles₁ A, c t = v := by
  classical

  let Nt : ℕ → A := fun n => ∑ i ∈ Finset.range n, A.ρ (t ^ i) v
  let Nf : ℕ → A := fun n => ∑ i ∈ Finset.range n, A.ρ (φ ^ i) w
  have Nt_zero : Nt 0 = 0 := Finset.sum_range_zero _
  have Nf_zero : Nf 0 = 0 := Finset.sum_range_zero _
  have Nt_one : Nt 1 = v := by
    change ∑ i ∈ Finset.range 1, A.ρ (t ^ i) v = v
    rw [Finset.sum_range_one, pow_zero, map_one, Module.End.one_apply]
  have Nt_add : ∀ a b : ℕ, Nt (a + b) = Nt a + A.ρ (t ^ a) (Nt b) := by
    intro a b
    change ∑ i ∈ Finset.range (a + b), A.ρ (t ^ i) v
      = ∑ i ∈ Finset.range a, A.ρ (t ^ i) v + A.ρ (t ^ a) (∑ i ∈ Finset.range b, A.ρ (t ^ i) v)
    rw [Finset.sum_range_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add, map_mul, Module.End.mul_apply]
  have Nf_add : ∀ a b : ℕ, Nf (a + b) = Nf a + A.ρ (φ ^ a) (Nf b) := by
    intro a b
    change ∑ i ∈ Finset.range (a + b), A.ρ (φ ^ i) w
      = ∑ i ∈ Finset.range a, A.ρ (φ ^ i) w + A.ρ (φ ^ a) (∑ i ∈ Finset.range b, A.ρ (φ ^ i) w)
    rw [Finset.sum_range_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add, map_mul, Module.End.mul_apply]
  have Nt_succ : ∀ a : ℕ, Nt (a + 1) = Nt a + A.ρ (t ^ a) v := by
    intro a; rw [Nt_add, Nt_one]
  have Nf_one : Nf 1 = w := by
    change ∑ i ∈ Finset.range 1, A.ρ (φ ^ i) w = w
    rw [Finset.sum_range_one, pow_zero, map_one, Module.End.one_apply]
  have Nf_succ : ∀ a : ℕ, Nf (a + 1) = Nf a + A.ρ (φ ^ a) w := by
    intro a; rw [Nf_add, Nf_one]

  have Nt_e_mul : ∀ n : ℕ, Nt (orderOf t * n) = 0 := by
    intro n
    induction n with
    | zero => rw [mul_zero]; exact Nt_zero
    | succ n ih =>
      rw [mul_add, mul_one, Nt_add, ih, zero_add]
      exact (congrArg (A.ρ (t ^ (orderOf t * n))) hNe).trans (map_zero _)
  have Nt_j_mul : ∀ n : ℕ, Nt (jo * n) = 0 := by
    intro n
    induction n with
    | zero => rw [mul_zero]; exact Nt_zero
    | succ n ih =>
      rw [mul_add, mul_one, Nt_add, ih, zero_add]
      exact (congrArg (A.ρ (t ^ (jo * n))) hNj).trans (map_zero _)
  have Nf_f_mul : ∀ n : ℕ, Nf (fo * n) = 0 := by
    intro n
    induction n with
    | zero => rw [mul_zero]; exact Nf_zero
    | succ n ih =>
      rw [mul_add, mul_one, Nf_add, ih, zero_add]
      change A.ρ (φ ^ (fo * n)) (∑ i ∈ Finset.range fo, A.ρ (φ ^ i) w) = 0
      rw [← LinearMap.sum_apply, hNφ, LinearMap.zero_apply, map_zero]

  have Nt_mod : ∀ n : ℕ, Nt n = Nt (n % orderOf t) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n (orderOf t), Nt_add, Nt_e_mul, map_zero, add_zero]
  have Nt_congr : ∀ {b b' : ℕ}, t ^ b = t ^ b' → Nt b = Nt b' := by
    intro b b' h
    rw [pow_eq_pow_iff_modEq] at h
    rw [Nt_mod b, Nt_mod b', h]

  have hcomm1 : ∀ b : ℕ, t ^ b * φ = φ * t ^ (b * m) := by
    intro b
    have h1 : φ⁻¹ * t ^ b * φ = t ^ (b * m) := by
      rw [pow_mul', ← hm, show φ⁻¹ * t * φ = φ⁻¹ * t * φ⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
    rw [← h1]; group
  have hcomm : ∀ a b : ℕ, t ^ b * φ ^ a = φ ^ a * t ^ (b * m ^ a) := by
    intro a
    induction a with
    | zero => intro b; rw [pow_zero, pow_zero, mul_one, one_mul, mul_one]
    | succ a ih =>
      intro b
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hcomm1, ← mul_assoc, pow_succ, mul_assoc (b)]

  have hw' : A.ρ φ (Nt m) = v + (A.ρ t w - w) := by
    rw [hw]; abel
  have key1 : ∀ b : ℕ, A.ρ φ (Nt (b * m)) = Nt b + (A.ρ (t ^ b) w - w) := by
    intro b
    induction b with
    | zero => rw [zero_mul, Nt_zero, map_zero, pow_zero, map_one, Module.End.one_apply, sub_self, add_zero]
    | succ b ih =>
      rw [add_mul, one_mul, Nt_add, map_add, ih, Nt_succ]
      have : A.ρ φ (A.ρ (t ^ (b * m)) (Nt m)) = A.ρ (t ^ b) (A.ρ φ (Nt m)) := by
        rw [← Module.End.mul_apply, ← map_mul, ← hcomm1, map_mul, Module.End.mul_apply]
      rw [this, hw', map_add, map_sub, ← Module.End.mul_apply (A.ρ (t ^ b)) (A.ρ t), ← map_mul,
        ← pow_succ]
      abel
  have key : ∀ a b : ℕ, A.ρ (φ ^ a) (Nt (b * m ^ a)) = Nt b + (A.ρ (t ^ b) (Nf a) - Nf a) := by
    intro a
    induction a with
    | zero =>
      intro b
      rw [pow_zero, pow_zero, mul_one, map_one, Module.End.one_apply, Nf_zero, map_zero, sub_self, add_zero]
    | succ a ih =>
      intro b
      rw [pow_succ, map_mul, Module.End.mul_apply, pow_succ, ← mul_assoc, key1 (b * m ^ a), map_add, ih,
        Nf_succ, map_add, map_sub]
      have : A.ρ (φ ^ a) (A.ρ (t ^ (b * m ^ a)) w) = A.ρ (t ^ b) (A.ρ (φ ^ a) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply]
      rw [this]
      abel

  let E : ℕ → ℕ → A := fun a b => Nf a + A.ρ (φ ^ a) (Nt b)
  have hE : ∀ a b a' b' : ℕ, φ ^ a * t ^ b = φ ^ a' * t ^ b' → E a b = E a' b' := by

    suffices H : ∀ a b a' b' : ℕ, a ≤ a' → φ ^ a * t ^ b = φ ^ a' * t ^ b' → E a b = E a' b' by
      intro a b a' b' h
      rcases le_total a a' with hle | hle
      · exact H a b a' b' hle h
      · exact (H a' b' a b hle h.symm).symm
    intro a b a' b' hle h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle

    have h1 : t ^ b = φ ^ d * t ^ b' := by
      rw [pow_add, mul_assoc] at h
      exact mul_left_cancel h
    have hd : φ ^ d ∈ Subgroup.zpowers t := by
      have : φ ^ d = t ^ b * (t ^ b')⁻¹ := by rw [h1]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers t b)
        (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers t b'))
    obtain ⟨n, rfl⟩ := hmin d hd
    have hφd : φ ^ (fo * n) = t ^ (jo * n) := by rw [pow_mul, hrel, ← pow_mul]
    rw [hφd, ← pow_add] at h1
    have hNt : Nt b = A.ρ (t ^ (jo * n)) (Nt b') := by
      rw [Nt_congr h1, Nt_add, Nt_j_mul, zero_add]
    change Nf a + A.ρ (φ ^ a) (Nt b) = Nf (a + fo * n) + A.ρ (φ ^ (a + fo * n)) (Nt b')
    rw [Nf_add, Nf_f_mul, map_zero, add_zero, pow_add, hφd, map_mul, Module.End.mul_apply, hNt]
  have hex : ∀ x : G, ∃ ab : ℕ × ℕ, x = φ ^ ab.1 * t ^ ab.2 := fun x => by
    obtain ⟨a, b, h⟩ := hgen x; exact ⟨(a, b), h⟩
  let nf : G → ℕ × ℕ := fun x => Classical.choose (hex x)
  have hnf : ∀ x, x = φ ^ (nf x).1 * t ^ (nf x).2 := fun x => Classical.choose_spec (hex x)
  let c : G → A := fun x => E (nf x).1 (nf x).2
  have hc : ∀ a b : ℕ, c (φ ^ a * t ^ b) = E a b := by
    intro a b
    exact hE _ _ _ _ (hnf (φ ^ a * t ^ b)).symm
  have hcoc : c ∈ cocycles₁ A := by
    rw [mem_cocycles₁_iff]
    intro x y
    obtain ⟨a, b, rfl⟩ := hgen x
    obtain ⟨a', b', rfl⟩ := hgen y
    have hxy : φ ^ a * t ^ b * (φ ^ a' * t ^ b') = φ ^ (a + a') * t ^ (b * m ^ a' + b') := by
      rw [pow_add, pow_add, mul_assoc, ← mul_assoc (t ^ b), hcomm a' b]; group
    rw [hxy, hc, hc, hc]
    change Nf (a + a') + A.ρ (φ ^ (a + a')) (Nt (b * m ^ a' + b'))
      = A.ρ (φ ^ a * t ^ b) (Nf a' + A.ρ (φ ^ a') (Nt b')) + (Nf a + A.ρ (φ ^ a) (Nt b))
    have e1 : A.ρ (φ ^ a') (A.ρ (t ^ (b * m ^ a')) (Nt b')) = A.ρ (t ^ b) (A.ρ (φ ^ a') (Nt b')) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply]
    rw [Nf_add, Nt_add, pow_add, map_mul, map_mul]
    simp only [Module.End.mul_apply, map_add]
    rw [key a' b, e1]
    simp only [map_add, map_sub]
    abel
  refine ⟨⟨c, hcoc⟩, ?_⟩
  change c t = v
  have : c t = E 0 1 := by
    have h := hc 0 1
    rwa [pow_zero, pow_one, one_mul] at h
  rw [this]
  change Nf 0 + A.ρ (φ ^ 0) (Nt 1) = v
  rw [Nf_zero, zero_add, pow_zero, map_one, Module.End.one_apply, Nt_one]

end S_groupCohomology_exists_cocycles1_apply_eq_of_frobenius_tame_relations
end P2MW
export P2MW.S_groupCohomology_exists_cocycles1_apply_eq_of_frobenius_tame_relations (solution)
