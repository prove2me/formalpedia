-- Prove2me | solution 1 for syracuse_uniform_descent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-10T19:14:41.869776+00:00
-- url     : https://prove2.me/submissions/f40406ec-10e2-4d04-bd67-a2ea7d183393

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem stepOdd (y : ℕ) : Odd (syracuseStep y) := by
  show Odd (ordCompl[2] (3 * y + 1))
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact Nat.not_dvd_ordCompl Nat.prime_two (by positivity)

theorem step_exact {m : ℕ} (hm : Odd m) :
    ∃ a : ℕ, 0 < a ∧ 2 ^ a * syracuseStep m = 3 * m + 1 := by
  refine ⟨(3 * m + 1).factorization 2, ?_, ?_⟩
  · have hne : 3 * m + 1 ≠ 0 := by positivity
    have hdvd : 2 ∣ 3 * m + 1 := by obtain ⟨k, rfl⟩ := hm; omega
    exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hne hdvd)
  · show 2 ^ ((3 * m + 1).factorization 2) * ordCompl[2] (3 * m + 1) = 3 * m + 1
    exact Nat.ordProj_mul_ordCompl_eq_self (3 * m + 1) 2

theorem exact_pow_iff_mod (x a : ℕ) :
    (∃ u, Odd u ∧ x = 2 ^ a * u) ↔ x % 2 ^ (a + 1) = 2 ^ a := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := hu
    have hrw : 2 ^ a * (2 * k + 1) = 2 ^ a + 2 ^ (a + 1) * k := by ring
    rw [hrw, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  · intro h
    have hx : x = 2 ^ (a + 1) * (x / 2 ^ (a + 1)) + 2 ^ a := by
      conv_lhs => rw [← Nat.div_add_mod x (2 ^ (a + 1))]
      rw [h]
    set q := x / 2 ^ (a + 1) with hq
    refine ⟨2 * q + 1, Nat.odd_iff.mpr (by omega), ?_⟩
    conv_lhs => rw [hx]
    ring

/-- Uniqueness of the `2`-adic factorisation into a power of two and an odd part. -/
theorem pow_two_unique {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have key : ∀ a b u v : ℕ, a ≤ b → Odd u → Odd v →
      2 ^ a * u = 2 ^ b * v → a = b ∧ u = v := by
    intro a b u v hab hu hv h
    have hb : b = a + (b - a) := by omega
    rw [hb, pow_add, mul_assoc] at h
    have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
    have hu' : u = 2 ^ (b - a) * v := Nat.eq_of_mul_eq_mul_left hpos h
    have hba : b - a = 0 := by
      by_contra hne
      have : 2 ∣ u := by
        rw [hu']
        exact Dvd.dvd.mul_right (dvd_pow_self 2 hne) v
      rw [Nat.odd_iff] at hu; omega
    constructor
    · omega
    · rw [hu', hba]; simp
  rcases le_total a b with hab | hab
  · exact key a b u v hab hu hv h
  · obtain ⟨h1, h2⟩ := key b a v u hab hv hu h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- **Step congruence.**  If `m ≡ m' (mod 2^K)` and the first Syracuse step of `m`
strips exactly `2^a` with `a + 1 ≤ K`, then the step of `m'` strips exactly `2^a` too. -/
theorem step_congr {m m' K a : ℕ} (hm : Odd m) (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (ha : 2 ^ a * syracuseStep m = 3 * m + 1)
    (hak : a + 1 ≤ K) :
    2 ^ a * syracuseStep m' = 3 * m' + 1 := by
  -- `3m+1` has exact power `2^a`
  have h1 : (3 * m + 1) % 2 ^ (a + 1) = 2 ^ a :=
    (exact_pow_iff_mod _ a).mp ⟨syracuseStep m, stepOdd m, ha.symm⟩
  -- transport the congruence down to modulus `2^(a+1)`
  have hdvd : (2 : ℕ) ^ (a + 1) ∣ 2 ^ K := pow_dvd_pow 2 hak
  have h2 : 3 * m + 1 ≡ 3 * m' + 1 [MOD 2 ^ (a + 1)] :=
    ((hcong.mul_left 3).add_right 1).of_dvd hdvd
  have h3 : (3 * m' + 1) % 2 ^ (a + 1) = 2 ^ a := by
    rw [← h2]; exact h1
  obtain ⟨u', hu', hxu⟩ := (exact_pow_iff_mod (3 * m' + 1) a).mpr h3
  obtain ⟨a', _, ha'⟩ := step_exact hm'
  obtain ⟨haa, huu⟩ := pow_two_unique hu' (stepOdd m') (hxu ▸ ha'.symm)
  rw [hxu, huu]

/-- The step congruence also propagates: the images stay congruent, with the modulus
reduced by exactly the power of two that was stripped. -/
theorem step_congr' {m m' K a : ℕ} (hm : Odd m) (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (ha : 2 ^ a * syracuseStep m = 3 * m + 1)
    (hak : a + 1 ≤ K) :
    2 ^ a * syracuseStep m' = 3 * m' + 1 ∧
      syracuseStep m ≡ syracuseStep m' [MOD 2 ^ (K - a)] := by
  have ha' := step_congr hm hm' hcong ha hak
  refine ⟨ha', ?_⟩
  have h1 : (2 : ℤ) ^ a * (syracuseStep m : ℤ) = 3 * (m : ℤ) + 1 := by exact_mod_cast ha
  have h2 : (2 : ℤ) ^ a * (syracuseStep m' : ℤ) = 3 * (m' : ℤ) + 1 := by exact_mod_cast ha'
  have hz : (2 ^ K : ℤ) ∣ (3 * (m' : ℤ) + 1) - (3 * (m : ℤ) + 1) := by
    have := (Nat.modEq_iff_dvd (n := 2 ^ K)).mp ((hcong.mul_left 3).add_right 1)
    push_cast at this
    exact this
  have hfac : (3 * (m' : ℤ) + 1) - (3 * (m : ℤ) + 1)
      = 2 ^ a * ((syracuseStep m' : ℤ) - (syracuseStep m : ℤ)) := by
    rw [← h1, ← h2]; ring
  rw [hfac] at hz
  have hKa : (2 : ℤ) ^ K = 2 ^ a * 2 ^ (K - a) := by
    rw [← pow_add]; congr 1; omega
  rw [hKa] at hz
  have hpos : (2 : ℤ) ^ a ≠ 0 := by positivity
  have hz2 : (2 ^ (K - a) : ℤ) ∣ ((syracuseStep m' : ℤ) - (syracuseStep m : ℤ)) :=
    (mul_dvd_mul_iff_left hpos).mp hz
  exact (Nat.modEq_iff_dvd (n := 2 ^ (K - a))).mpr (by push_cast; exact hz2)

theorem iterate_odd {m : ℕ} (hm : Odd m) : ∀ i, Odd (syracuseStep^[i] m) := by
  intro i
  induction i with
  | zero => simpa using hm
  | succ k _ => rw [Function.iterate_succ_apply']; exact stepOdd _

/-- **Terras uniformity.**  If `m ≡ m' (mod 2^K)` are odd and the first `t` Syracuse steps
of `m'` strip the exponents `a 0, …, a (t-1)` with total strictly below `K`, then the orbit
of `m` strips exactly the same exponents, and the orbits stay congruent modulo the
remaining budget. -/
theorem trajectory_congr (a : ℕ → ℕ) {m m' K : ℕ} (hm : Odd m) (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K]) (t : ℕ)
    (hstep : ∀ i < t, 2 ^ (a i) * (syracuseStep^[i + 1] m') = 3 * (syracuseStep^[i] m') + 1)
    (hbudget : (∑ i ∈ Finset.range t, a i) + 1 ≤ K) :
    ∀ i ≤ t,
      (syracuseStep^[i] m ≡ syracuseStep^[i] m' [MOD 2 ^ (K - ∑ j ∈ Finset.range i, a j)]) ∧
      (∀ j < i, 2 ^ (a j) * (syracuseStep^[j + 1] m) = 3 * (syracuseStep^[j] m) + 1) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨by simpa using hcong, by omega⟩
  | succ k ih =>
    intro hkt
    obtain ⟨hcongk, hstepk⟩ := ih (by omega)
    -- budget bookkeeping
    have hsub : Finset.range (k + 1) ⊆ Finset.range t := by
      intro x hx
      simp only [Finset.mem_range] at *
      omega
    have hmono : (∑ j ∈ Finset.range (k + 1), a j) ≤ ∑ i ∈ Finset.range t, a i :=
      Finset.sum_le_sum_of_subset hsub
    have hsplit : (∑ j ∈ Finset.range (k + 1), a j) = (∑ j ∈ Finset.range k, a j) + a k :=
      Finset.sum_range_succ a k
    have hak : a k + 1 ≤ K - ∑ j ∈ Finset.range k, a j := by omega
    -- apply the step congruence with the roles of m and m' exchanged
    obtain ⟨hstep_m, hcong_next⟩ :=
      step_congr' (m := syracuseStep^[k] m') (m' := syracuseStep^[k] m)
        (iterate_odd hm' k) (iterate_odd hm k) hcongk.symm
        (by have h := hstep k (by omega); rwa [Function.iterate_succ_apply'] at h) hak
    constructor
    · have hmod : K - ∑ j ∈ Finset.range (k + 1), a j
          = (K - ∑ j ∈ Finset.range k, a j) - a k := by omega
      rw [hmod, Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hcong_next.symm
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact hstepk j hlt
      · subst heq
        rw [Function.iterate_succ_apply']
        exact hstep_m

/-- The affine constant depends only on the exponent sequence, not on the starting point. -/
theorem affine_shared (a : ℕ → ℕ) (t : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, Odd m →
      (∀ j < t, 2 ^ (a j) * (syracuseStep^[j + 1] m) = 3 * (syracuseStep^[j] m) + 1) →
      2 ^ (∑ j ∈ Finset.range t, a j) * (syracuseStep^[t] m) = 3 ^ t * m + c := by
  induction t with
  | zero => exact ⟨0, by intro m _ _; simp⟩
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨3 * c + 2 ^ (∑ j ∈ Finset.range t, a j), ?_⟩
    intro m hm hsteps
    have hprev := hc m hm (fun j hj => hsteps j (by omega))
    have hlast := hsteps t (by omega)
    rw [Finset.sum_range_succ, pow_add, mul_assoc, hlast]
    have : 2 ^ (∑ j ∈ Finset.range t, a j) * (3 * syracuseStep^[t] m + 1)
        = 3 * (2 ^ (∑ j ∈ Finset.range t, a j) * syracuseStep^[t] m)
          + 2 ^ (∑ j ∈ Finset.range t, a j) := by ring
    rw [this, hprev]
    ring

/-- **Descent criterion.**  If the affine data of an orbit satisfies `3^t < 2^s` and the
additive constant is small compared to `m`, the orbit drops below its starting point. -/
theorem descent_of_affine {m c s t : ℕ}
    (h : 2 ^ s * (syracuseStep^[t] m) = 3 ^ t * m + c)
    (hgt : 3 ^ t < 2 ^ s) (hc : c < (2 ^ s - 3 ^ t) * m) :
    syracuseStep^[t] m < m := by
  by_contra hle
  rw [Nat.not_lt] at hle
  have h1 : 2 ^ s * m ≤ 2 ^ s * (syracuseStep^[t] m) := Nat.mul_le_mul_left _ hle
  rw [h] at h1
  have h2 : (2 ^ s - 3 ^ t) * m + 3 ^ t * m = 2 ^ s * m := by
    rw [← Nat.add_mul]; congr 1; omega
  omega

/-- **Uniform descent on a residue class.**  If one odd representative `m'` of a class mod
`2^K` drops below itself within `t` steps, and the total number of halvings used stays below
`K`, then *every* odd `m ≥ m'` in that class drops below itself in the same `t` steps. -/
theorem solution (a : ℕ → ℕ) (m m' K t : ℕ) (hm : Odd m) (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (hstep : ∀ i < t, 2 ^ (a i) * (syracuseStep^[i + 1] m') = 3 * (syracuseStep^[i] m') + 1)
    (hbudget : (∑ i ∈ Finset.range t, a i) + 1 ≤ K)
    (hgt : 3 ^ t < 2 ^ (∑ i ∈ Finset.range t, a i))
    (hdesc : syracuseStep^[t] m' < m')
    (hle : m' ≤ m) :
    syracuseStep^[t] m < m := by
  obtain ⟨c, hc⟩ := affine_shared a t
  set S := ∑ i ∈ Finset.range t, a i with hS
  -- the representative gives the bound on the affine constant
  have hm'aff := hc m' hm' hstep
  have hlt : 2 ^ S * (syracuseStep^[t] m') < 2 ^ S * m' :=
    mul_lt_mul_of_pos_left hdesc (Nat.two_pow_pos S)
  rw [hm'aff] at hlt
  have hcbound : c < (2 ^ S - 3 ^ t) * m' := by
    have : (2 ^ S - 3 ^ t) * m' + 3 ^ t * m' = 2 ^ S * m' := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  have hcbound' : c < (2 ^ S - 3 ^ t) * m :=
    lt_of_lt_of_le hcbound (Nat.mul_le_mul_left _ hle)
  -- transport the exponents to m, then apply the affine descent criterion
  have hsteps_m : ∀ j < t, 2 ^ (a j) * (syracuseStep^[j + 1] m) = 3 * (syracuseStep^[j] m) + 1 :=
    (trajectory_congr a hm hm' hcong t hstep hbudget t (le_refl t)).2
  exact descent_of_affine (hc m hm hsteps_m) hgt hcbound'
