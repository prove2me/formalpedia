-- Prove2me | solution 1 for exists_idempotent_tower_of_finite_quotient_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2e17a633-f7cf-51f6-a8bb-d133e9c2bdb4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_idempotent_tower_of_finite_quotient_of_isMaximal

set_option maxHeartbeats 1600000
set_option autoImplicit false

theorem solution
    {L : Type} [CommRing L] (ℓ : L) (hfin : Finite (L ⧸ Ideal.span {ℓ}))
    (𝔓 : Ideal L) [𝔓.IsMaximal] (hℓ : ℓ ∈ 𝔓)
    {T : Type} [CommRing T] (π : T →+* L)
    (hdense : ∀ (m : ℕ) (x : L), ∃ y : T, π y - x ∈ Ideal.span {ℓ ^ m}) :
    ∃ e : ℕ → T,
      (∀ m : ℕ, π (e m) * π (e m) - π (e m) ∈ Ideal.span {ℓ ^ m}) ∧
      (∀ m : ℕ, π (e (m + 1)) - π (e m) ∈ Ideal.span {ℓ ^ m}) ∧
      (∀ m : ℕ, 1 - π (e m) ∈ 𝔓) ∧
      (∀ (m : ℕ) (𝔪 : Ideal L), 𝔪.IsMaximal → ℓ ∈ 𝔪 → 𝔪 ≠ 𝔓 → π (e m) ∈ 𝔪) ∧
      (∀ m : ℕ, ∃ N : ℕ, ∀ x ∈ 𝔓 ^ N, π (e m) * x ∈ Ideal.span {ℓ ^ m}) := by
  classical

  set S := L ⧸ Ideal.span {ℓ} with hS
  let mk : L →+* S := Ideal.Quotient.mk (Ideal.span {ℓ})
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hmk0 : ∀ x : L, mk x = 0 ↔ ℓ ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  let P : Ideal S := 𝔓.map mk

  haveI : Fintype S := Fintype.ofFinite S
  haveI : Finite (Ideal S) := Finite.of_injective (fun I : Ideal S => (I : Set S)) SetLike.coe_injective
  obtain ⟨n, hn1, hPn⟩ : ∃ n : ℕ, 1 ≤ n ∧ P ^ (n + 1) = P ^ n := by
    obtain ⟨i, j, hij, hPij⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => P ^ (k + 1))
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨i + 1, Nat.succ_pos i |>.le.trans (le_refl _) |> fun _ => Nat.le_add_left 1 i, le_antisymm (Ideal.pow_le_pow_right (Nat.le_succ _)) ?_⟩
      calc P ^ (i + 1) = P ^ (j + 1) := hPij
        _ ≤ P ^ (i + 1 + 1) := Ideal.pow_le_pow_right (by omega)
    · refine ⟨j + 1, Nat.le_add_left 1 j, le_antisymm (Ideal.pow_le_pow_right (Nat.le_succ _)) ?_⟩
      calc P ^ (j + 1) = P ^ (i + 1) := hPij.symm
        _ ≤ P ^ (j + 1 + 1) := Ideal.pow_le_pow_right (by omega)
  have hPstab : ∀ k : ℕ, P ^ (n + k) = P ^ n := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, pow_succ, ih, ← pow_succ, hPn]
  have hPidem : P ^ n ≤ P ^ n • P ^ n := by
    rw [smul_eq_mul, ← pow_add, hPstab n]
  have hPfg : (P ^ n).FG := by
    refine Submodule.fg_def.mpr ⟨((P ^ n : Ideal S) : Set S), Set.toFinite _, ?_⟩
    exact Ideal.span_eq _

  obtain ⟨r, hr1, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (P ^ n) (P ^ n) hPfg hPidem

  obtain ⟨e₁, he₁⟩ := hmk r
  have hPn_map : P ^ n = (𝔓 ^ n).map mk := by rw [Ideal.map_pow]
  have hPn_le : 𝔓 ^ n ≤ 𝔓 := Ideal.pow_le_self (by omega)

  have ha : ℓ ∣ e₁ ^ 2 - e₁ := by
    rw [← hmk0, map_sub, map_pow, he₁]
    have h1 : 1 - r ∈ P ^ n := by
      have := (P ^ n).neg_mem hr1
      rwa [neg_sub] at this
    have h2 : r * (1 - r) = 0 := by
      have := hr0 (1 - r) h1
      rwa [smul_eq_mul] at this
    have : r ^ 2 - r = -(r * (1 - r)) := by ring
    rw [this, h2, neg_zero]

  have hb : 1 - e₁ ∈ 𝔓 := by
    have h1 : mk (1 - e₁) ∈ (𝔓 ^ n).map mk := by
      rw [← hPn_map, map_sub, map_one, he₁]
      have := (P ^ n).neg_mem hr1
      rwa [neg_sub] at this
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective mk hmk).1 h1
    have hdiff : ℓ ∣ (1 - e₁) - x := by
      rw [← hmk0, map_sub, hxe, sub_self]
    obtain ⟨c, hc⟩ := hdiff
    have : 1 - e₁ = x + ℓ * c := by rw [← hc]; ring
    rw [this]
    exact 𝔓.add_mem (hPn_le hx) (𝔓.mul_mem_right c hℓ)

  have hd : ∀ x ∈ 𝔓 ^ n, ℓ ∣ e₁ * x := by
    intro x hx
    rw [← hmk0, map_mul, he₁]
    have hx' : mk x ∈ P ^ n := by rw [hPn_map]; exact Ideal.mem_map_of_mem mk hx
    have := hr0 (mk x) hx'
    rwa [smul_eq_mul] at this

  have hc : ∀ 𝔪 : Ideal L, 𝔪.IsMaximal → ℓ ∈ 𝔪 → 𝔪 ≠ 𝔓 → e₁ ∈ 𝔪 := by
    intro 𝔪 h𝔪 hℓ𝔪 hne
    by_contra he
    apply hne
    have hle : 𝔓 ≤ 𝔪 := by
      intro x hx
      have hxn : x ^ n ∈ 𝔓 ^ n := Ideal.pow_mem_pow hx n
      obtain ⟨c, hc⟩ := hd (x ^ n) hxn
      have hmem : e₁ * x ^ n ∈ 𝔪 := by rw [hc]; exact 𝔪.mul_mem_right c hℓ𝔪
      have := (h𝔪.isPrime.mem_or_mem hmem).resolve_left he
      exact h𝔪.isPrime.mem_of_pow_mem n this
    exact (Ideal.IsMaximal.eq_of_le inferInstance h𝔪.ne_top hle).symm

  let F : ℕ → L := fun k => Nat.rec e₁ (fun _ e => 3 * e ^ 2 - 2 * e ^ 3) k
  have hF0 : F 0 = e₁ := rfl
  have hFs : ∀ k, F (k + 1) = 3 * F k ^ 2 - 2 * F k ^ 3 := fun k => rfl
  have hF1 : ∀ k, ℓ ^ (k + 1) ∣ F k ^ 2 - F k := by
    intro k
    induction k with
    | zero => simpa [hF0] using ha
    | succ k ih =>
        rw [hFs]
        have key : (3 * F k ^ 2 - 2 * F k ^ 3) ^ 2 - (3 * F k ^ 2 - 2 * F k ^ 3)
            = (4 * F k ^ 2 - 4 * F k - 3) * ((F k ^ 2 - F k) * (F k ^ 2 - F k)) := by ring
        rw [key]
        refine dvd_mul_of_dvd_right ?_ _
        have h2 : ℓ ^ (k + 1 + 1) ∣ ℓ ^ (k + 1) * ℓ ^ (k + 1) := by
          rw [← pow_add]; exact pow_dvd_pow ℓ (by omega)
        exact h2.trans (mul_dvd_mul ih ih)
  have hF2 : ∀ k, ℓ ^ (k + 1) ∣ F (k + 1) - F k := by
    intro k
    rw [hFs]
    have key : 3 * F k ^ 2 - 2 * F k ^ 3 - F k = (1 - 2 * F k) * (F k ^ 2 - F k) := by ring
    rw [key]
    exact dvd_mul_of_dvd_right (hF1 k) _
  have hF3 : ∀ k, ℓ ∣ F k - e₁ := by
    intro k
    induction k with
    | zero => simp [hF0]
    | succ k ih =>
        have : F (k + 1) - e₁ = (F (k + 1) - F k) + (F k - e₁) := by ring
        rw [this]
        exact dvd_add ((dvd_pow_self ℓ (Nat.succ_ne_zero k)).trans (hF2 k)) ih

  choose e he using fun m => hdense (m + 1) (F m)
  have he' : ∀ m, ℓ ^ (m + 1) ∣ π (e m) - F m := fun m => Ideal.mem_span_singleton.1 (he m)
  have hℓdvd : ∀ {x : L} (𝔪 : Ideal L), ℓ ∈ 𝔪 → ℓ ∣ x → x ∈ 𝔪 := by
    intro x 𝔪 hℓ𝔪 hx
    obtain ⟨c, rfl⟩ := hx
    exact 𝔪.mul_mem_right c hℓ𝔪
  have hpow1 : ∀ m : ℕ, ℓ ∣ ℓ ^ (m + 1) := fun m => dvd_pow_self ℓ (Nat.succ_ne_zero m)

  have hidem : ∀ m, ℓ ^ m ∣ π (e m) * π (e m) - π (e m) := by
    intro m
    have key : π (e m) * π (e m) - π (e m)
        = (F m ^ 2 - F m) + (π (e m) - F m) * (2 * F m + (π (e m) - F m) - 1) := by ring
    rw [key]
    exact ((pow_dvd_pow ℓ (Nat.le_succ m)).trans (hF1 m)).add
      (dvd_mul_of_dvd_left ((pow_dvd_pow ℓ (Nat.le_succ m)).trans (he' m)) _)
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact Ideal.mem_span_singleton.2 (hidem m)
  · intro m
    apply Ideal.mem_span_singleton.2
    have key : π (e (m + 1)) - π (e m)
        = (π (e (m + 1)) - F (m + 1)) + (F (m + 1) - F m) - (π (e m) - F m) := by ring
    rw [key]
    refine ((?_ : ℓ ^ m ∣ _).add ?_).sub ?_
    · exact (pow_dvd_pow ℓ (by omega)).trans (he' (m + 1))
    · exact (pow_dvd_pow ℓ (Nat.le_succ m)).trans (hF2 m)
    · exact (pow_dvd_pow ℓ (Nat.le_succ m)).trans (he' m)
  · intro m
    have key : 1 - π (e m) = (1 - e₁) - (F m - e₁) - (π (e m) - F m) := by ring
    rw [key]
    exact 𝔓.sub_mem (𝔓.sub_mem hb (hℓdvd 𝔓 hℓ (hF3 m))) (hℓdvd 𝔓 hℓ ((hpow1 m).trans (he' m)))
  · intro m 𝔪 h𝔪 hℓ𝔪 hne
    have key : π (e m) = e₁ + (F m - e₁) + (π (e m) - F m) := by ring
    rw [key]
    exact 𝔪.add_mem (𝔪.add_mem (hc 𝔪 h𝔪 hℓ𝔪 hne) (hℓdvd 𝔪 hℓ𝔪 (hF3 m)))
      (hℓdvd 𝔪 hℓ𝔪 ((hpow1 m).trans (he' m)))
  · intro m

    set g := π (e m) with hg
    have hg1 : ∀ x ∈ 𝔓 ^ n, ℓ ∣ g * x := by
      intro x hx
      have key : g * x = e₁ * x + ((F m - e₁) + (g - F m)) * x := by ring
      rw [key]
      exact (hd x hx).add (dvd_mul_of_dvd_left ((hF3 m).add ((hpow1 m).trans (he' m))) _)
    have hgk : ∀ k : ℕ, ∀ x ∈ (𝔓 ^ n) ^ k, ℓ ^ k ∣ g ^ k * x := by
      intro k
      induction k with
      | zero => intro x _; simp
      | succ k ih =>
          intro x hx
          rw [pow_succ] at hx
          refine Submodule.mul_induction_on hx ?_ ?_
          · intro a ha b hb
            have key : g ^ (k + 1) * (a * b) = (g ^ k * a) * (g * b) := by ring
            rw [key, pow_succ]
            exact mul_dvd_mul (ih a ha) (hg1 b hb)
          · intro x y hx hy
            rw [mul_add]
            exact hx.add hy
    have hgpow : ∀ k : ℕ, ℓ ^ m ∣ g ^ (k + 1) - g := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have key : g ^ (k + 1 + 1) - g = g ^ k * (g * g - g) + (g ^ (k + 1) - g) := by ring
          rw [key]
          exact (dvd_mul_of_dvd_right (hidem m) _).add ih
    refine ⟨n * m, fun x hx => Ideal.mem_span_singleton.2 ?_⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, pow_zero]; exact one_dvd _
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
      rw [pow_mul] at hx
      have h1 : ℓ ^ m ∣ g ^ m * x := hgk m x hx
      have h2 : ℓ ^ m ∣ (g ^ m - g) * x := by
        refine dvd_mul_of_dvd_left ?_ _
        have := hgpow k
        rwa [show k + 1 = m by omega] at this
      have key : g * x = g ^ m * x - (g ^ m - g) * x := by ring
      rw [key]
      exact h1.sub h2

end S_exists_idempotent_tower_of_finite_quotient_of_isMaximal
end P2MW
export P2MW.S_exists_idempotent_tower_of_finite_quotient_of_isMaximal (solution)
