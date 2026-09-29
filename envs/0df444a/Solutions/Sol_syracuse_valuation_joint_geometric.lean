-- Prove2me | solution 1 for syracuse_valuation_joint_geometric
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T07:38:16.822287+00:00
-- url     : https://prove2.me/submissions/cbb840ef-276f-49c2-bf93-9848d22bf9c9

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_valuation_tail_almost_uniform

set_option autoImplicit false

open MeasureTheory Set Nat
open scoped BigOperators

namespace CollatzJointPackage



set_option autoImplicit false

open Nat

private lemma two_dvd_three_mul_add_one_of_odd {n : ℕ} (hn : Odd n) :
    2 ∣ 3 * n + 1 := by
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  refine ⟨3 * k + 2, ?_⟩
  omega

/-- Every positive Syracuse successor is positive. -/
theorem syracuse_step_pos {n : ℕ} (hn : 0 < n) : 0 < syracuseStep n := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.ordCompl_pos
  exact hpos.ne'

/-- Every positive Syracuse successor is odd. -/
theorem syracuse_step_odd {n : ℕ} (hn : 0 < n) : Odd (syracuseStep n) := by
  have hpos : 0 < 3 * n + 1 := by omega
  have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
    Nat.coprime_ordCompl Nat.prime_two hpos.ne'
  exact hcop.odd_of_left

/-- An odd positive input has a positive 2-adic exponent in its Syracuse numerator. -/
theorem syracuse_step_factorization_pos {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < (3 * n + 1).factorization 2 := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
  · exact hpos.ne'
  · exact two_dvd_three_mul_add_one_of_odd hodd

/-- The valuation-weighted Syracuse recurrence. -/
theorem syracuse_step_factorization_mul {n : ℕ} :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  simpa [syracuseStep] using Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/- The three adapter facts are often consumed together on positive odd inputs. -/
theorem syracuse_step_pos_odd_valuation {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < syracuseStep n ∧ Odd (syracuseStep n) ∧
      0 < (3 * n + 1).factorization 2 ∧
        2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact ⟨syracuse_step_pos hn, syracuse_step_odd hn,
    syracuse_step_factorization_pos hn hodd, syracuse_step_factorization_mul⟩





set_option autoImplicit false

open scoped BigOperators

/-- The exact exponent used by the `i`-th accelerated Syracuse step. -/
def syracuseExponent (N i : ℕ) : ℕ :=
  (3 * (syracuseStep^[i]) N + 1).factorization 2

/-- Positive oddness propagates through every forward Syracuse iterate. -/
theorem syracuse_iterate_pos_odd (N : ℕ) (hN : 0 < N) (hodd : Odd N) (i : ℕ) :
    0 < (syracuseStep^[i]) N ∧ Odd ((syracuseStep^[i]) N) := by
  induction i with
  | zero =>
      simpa using And.intro hN hodd
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨syracuse_step_pos ih.1, syracuse_step_odd ih.1⟩

/-- Every exponent in the positive odd Syracuse orbit is positive. -/
theorem syracuse_exponent_pos (N i : ℕ) (hN : 0 < N) (hodd : Odd N) :
    0 < syracuseExponent N i := by
  unfold syracuseExponent
  obtain ⟨hi_pos, hi_odd⟩ := syracuse_iterate_pos_odd N hN hodd i
  exact syracuse_step_factorization_pos hi_pos hi_odd

/-- Each consecutive pair in the orbit satisfies the exact valuation recurrence. -/
theorem syracuse_exponent_chain (N i : ℕ) :
    2 ^ syracuseExponent N i * (syracuseStep^[i + 1]) N =
      3 * (syracuseStep^[i]) N + 1 := by
  simpa [syracuseExponent, Function.iterate_succ_apply'] using
    (syracuse_step_factorization_mul (n := (syracuseStep^[i]) N))

/-- A positive threshold crossed by a finite partial sum has a first crossing. -/
theorem exists_first_crossing (a : ℕ → ℕ) :
    ∀ (t q : ℕ), 0 < q → q ≤ ∑ i ∈ Finset.range t, a i →
      ∃ k < t,
        (∑ i ∈ Finset.range k, a i) < q ∧
          q ≤ (∑ i ∈ Finset.range k, a i) + a k
  | 0, q, hq, hsum => by
      simp at hsum
      omega
  | t + 1, q, hq, hsum => by
      by_cases hprefix : q ≤ ∑ i ∈ Finset.range t, a i
      · obtain ⟨k, hkt, hlt, hcross⟩ := exists_first_crossing a t q hq hprefix
        exact ⟨k, lt_trans hkt (Nat.lt_succ_self t), hlt, hcross⟩
      · have hlt : (∑ i ∈ Finset.range t, a i) < q := Nat.lt_of_not_ge hprefix
        refine ⟨t, Nat.lt_succ_self t, hlt, ?_⟩
        simpa [Finset.sum_range_succ] using hsum





set_option autoImplicit false

open Nat

/-- Exactness of the exponent in `3 * n + 1` is equivalent to an odd
quotient, not merely to divisibility by the corresponding power of two. -/
theorem syracuse_factorization_two_iff_odd_quotient (n a : ℕ) :
    (3 * n + 1).factorization 2 = a ↔
      ∃ m : ℕ, Odd m ∧ 2 ^ a * m = 3 * n + 1 := by
  have hpos : 0 < 3 * n + 1 := by omega
  constructor
  · intro ha
    have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
      Nat.coprime_ordCompl Nat.prime_two hpos.ne'
    refine ⟨syracuseStep n, ?_, ?_⟩
    · simpa [syracuseStep] using hcop.odd_of_left
    · simpa [ha] using (syracuse_step_factorization_mul (n := n))
  · rintro ⟨m, hmodd, hmul⟩
    have hpowdvd : 2 ^ a ∣ 3 * n + 1 := ⟨m, hmul.symm⟩
    have hle : a ≤ (3 * n + 1).factorization 2 := by
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mp hpowdvd
    have hnotdvd : ¬2 ^ (a + 1) ∣ 3 * n + 1 := by
      intro hdiv
      rcases hdiv with ⟨k, hk⟩
      have hcancel : 2 * k = m := by
        apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
        calc
          2 ^ a * (2 * k) = 2 ^ (a + 1) * k := by
            simp [pow_succ, Nat.mul_assoc]
          _ = 3 * n + 1 := hk.symm
          _ = 2 ^ a * m := hmul.symm
      obtain ⟨j, hj⟩ := hmodd
      omega
    have hnotle : ¬a + 1 ≤ (3 * n + 1).factorization 2 := by
      intro h
      apply hnotdvd
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mpr h
    omega





set_option autoImplicit false

open Nat
open scoped BigOperators

/- The affine numerator is kept in a form whose head/tail decomposition is
   immediate.  For `as = [a₀, ..., aₖ]`, it equals
   `3^as.length * N` plus the usual weighted prefix-power constant. -/
def syracuseAffineConstant : List ℕ → ℕ
  | [] => 0
  | a :: as => 3 ^ as.length + 2 ^ a * syracuseAffineConstant as

def syracuseAffineNumerator (as : List ℕ) (N : ℕ) : ℕ :=
  3 ^ as.length * N + syracuseAffineConstant as

def syracuseExactValuationPrefix (N : ℕ) : List ℕ → Prop
  | [] => True
  | a :: as => syracuseExponent N 0 = a ∧
      syracuseExactValuationPrefix (syracuseStep N) as

lemma syracuseAffineNumerator_shift (as : List ℕ) (N : ℕ) :
    syracuseAffineNumerator as N =
      3 ^ as.length * N + syracuseAffineNumerator as 0 := by
  simp [syracuseAffineNumerator]

lemma syracuseAffineNumerator_cons (a : ℕ) (as : List ℕ) (N : ℕ) :
    syracuseAffineNumerator (a :: as) N =
      3 ^ as.length * (3 * N + 1) +
        2 ^ a * syracuseAffineNumerator as 0 := by
  simp [syracuseAffineNumerator, syracuseAffineConstant, pow_succ]
  ring

lemma syracuseAffineConstant_cons_odd (a : ℕ) (as : List ℕ) (ha : 0 < a) :
    Odd (syracuseAffineConstant (a :: as)) := by
  simp only [syracuseAffineConstant]
  apply Odd.add_even
  · exact Odd.pow (by decide : Odd (3 : ℕ))
  · exact ((show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
      (by omega : a ≠ 0)).mul_right _

lemma syracuse_exponent_step_shift (N i : ℕ) :
    syracuseExponent (syracuseStep N) i = syracuseExponent N (i + 1) := by
  simp only [syracuseExponent]
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem syracuse_exact_valuation_prefix_iff
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) (as : List ℕ)
    (ha : ∀ a ∈ as, 0 < a) :
    syracuseExactValuationPrefix N as ↔
      ∃ m : ℕ, Odd m ∧
        2 ^ as.sum * m = syracuseAffineNumerator as N := by
  induction as generalizing N with
  | nil =>
      constructor
      · intro _
        exact ⟨N, hodd, by simp [syracuseAffineNumerator, syracuseAffineConstant]⟩
      · rintro ⟨m, hm, _⟩
        trivial
  | cons a as ih =>
      have ha0 : 0 < a := ha a (by simp)
      have harest : ∀ b ∈ as, 0 < b := by
        intro b hb
        exact ha b (by simp [hb])
      constructor
      · rintro ⟨hhead, htail⟩
        have hstep_pos : 0 < syracuseStep N := syracuse_step_pos hN
        have hstep_odd : Odd (syracuseStep N) := syracuse_step_odd hN
        obtain ⟨m, hm, htailEq⟩ :=
          (ih (N := syracuseStep N) hstep_pos hstep_odd harest).mp htail
        have hchain : 2 ^ a * syracuseStep N = 3 * N + 1 := by
          calc
            2 ^ a * syracuseStep N =
                2 ^ syracuseExponent N 0 * syracuseStep N := by rw [hhead]
            _ = 3 * N + 1 := by simpa using syracuse_exponent_chain N 0
        refine ⟨m, hm, ?_⟩
        calc
          2 ^ (a :: as).sum * m =
              2 ^ a * (2 ^ as.sum * m) := by
                simp [List.sum_cons, pow_add]
                ring
          _ = 2 ^ a * syracuseAffineNumerator as (syracuseStep N) := by
                rw [htailEq]
          _ = 2 ^ a *
                (3 ^ as.length * syracuseStep N +
                  syracuseAffineNumerator as 0) := by
                rw [syracuseAffineNumerator_shift]
          _ = 3 ^ as.length * (3 * N + 1) +
                2 ^ a * syracuseAffineNumerator as 0 := by
                rw [← hchain]
                ring
          _ = syracuseAffineNumerator (a :: as) N := by
                symm
                exact syracuseAffineNumerator_cons a as N
      · rintro ⟨m, hm, hEq⟩
        have hEq' :
            2 ^ (a + as.sum) * m = syracuseAffineNumerator (a :: as) N := by
          simpa [List.sum_cons] using hEq
        let x : ℕ := 2 ^ as.sum * m
        have hAeq : syracuseAffineNumerator (a :: as) N = 2 ^ a * x := by
          calc
            syracuseAffineNumerator (a :: as) N = 2 ^ (a + as.sum) * m := hEq'.symm
            _ = 2 ^ a * x := by
              simp [x, pow_add]
              ring
        have hAdiv : 2 ^ a ∣ syracuseAffineNumerator (a :: as) N :=
          ⟨x, hAeq⟩
        have hsumdiv :
            2 ^ a ∣ 3 ^ as.length * (3 * N + 1) +
              2 ^ a * syracuseAffineNumerator as 0 := by
          rw [syracuseAffineNumerator_cons] at hAdiv
          exact hAdiv
        have hCdiv : 2 ^ a ∣ 2 ^ a * syracuseAffineNumerator as 0 :=
          dvd_mul_right _ _
        have hsumdiv' :
            2 ^ a ∣ 2 ^ a * syracuseAffineNumerator as 0 +
              3 ^ as.length * (3 * N + 1) := by
          simpa [Nat.add_comm] using hsumdiv
        have hXdiv : 2 ^ a ∣ 3 ^ as.length * (3 * N + 1) := by
          simpa using (Nat.dvd_add_iff_right hCdiv).mpr hsumdiv'
        have hcop : Nat.Coprime (2 ^ a) (3 ^ as.length) := by
          exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)
        have hheadDiv : 2 ^ a ∣ 3 * N + 1 :=
          (hcop.dvd_mul_left).mp hXdiv
        obtain ⟨y, hy⟩ := hheadDiv
        have hy_pos : 0 < y := by
          have hy_ne : y ≠ 0 := by
            intro hy0
            subst y
            simp at hy
          exact Nat.pos_of_ne_zero hy_ne
        have hrel : x = 3 ^ as.length * y + syracuseAffineNumerator as 0 := by
          apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
          calc
            2 ^ a * x = syracuseAffineNumerator (a :: as) N := hAeq.symm
            _ = 3 ^ as.length * (3 * N + 1) +
                2 ^ a * syracuseAffineNumerator as 0 :=
                  syracuseAffineNumerator_cons a as N
            _ = 3 ^ as.length * (2 ^ a * y) +
                2 ^ a * syracuseAffineNumerator as 0 := by rw [hy]
            _ = 2 ^ a *
                (3 ^ as.length * y + syracuseAffineNumerator as 0) := by
                  ring
        have hy_odd : Odd y := by
          cases as with
          | nil =>
              have hy_eq : y = m := by
                calc
                  y = x := by
                    simpa [syracuseAffineNumerator, syracuseAffineConstant] using hrel.symm
                  _ = m := by simp [x]
              simpa [hy_eq] using hm
          | cons b bs =>
              have hb : 0 < b := harest b (by simp)
              have hsum_pos : 0 < (b :: bs).sum := by
                simp [List.sum_cons]
                omega
              have hx_even : Even x := by
                have hp : Even (2 ^ (b :: bs).sum) :=
                  (show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
                    (by omega : (b :: bs).sum ≠ 0)
                exact hp.mul_right m
              have hCodd : Odd (syracuseAffineConstant (b :: bs)) :=
                syracuseAffineConstant_cons_odd b bs hb
              have hCodd' : Odd (syracuseAffineNumerator (b :: bs) 0) := by
                simpa [syracuseAffineNumerator] using hCodd
              have hadd_even :
                  Even (3 ^ (b :: bs).length * y +
                    syracuseAffineNumerator (b :: bs) 0) := by
                rw [← hrel]
                exact hx_even
              have hprod_odd : Odd (3 ^ (b :: bs).length * y) :=
                (even_add').mp hadd_even |>.mpr hCodd'
              exact hprod_odd.of_mul_right
        have hhead : syracuseExponent N 0 = a := by
          simpa [syracuseExponent] using
            (syracuse_factorization_two_iff_odd_quotient N a).mpr
              ⟨y, hy_odd, hy.symm⟩
        have hy_step : y = syracuseStep N := by
          apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
          calc
            2 ^ a * y = 3 * N + 1 := hy.symm
            _ = 2 ^ a * syracuseStep N := by
              rw [← hhead]
              simpa using (syracuse_exponent_chain N 0).symm
        have htailEq :
            2 ^ as.sum * m = syracuseAffineNumerator as y := by
          calc
            2 ^ as.sum * m = x := by rfl
            _ = 3 ^ as.length * y + syracuseAffineNumerator as 0 := hrel
            _ = syracuseAffineNumerator as y :=
              (syracuseAffineNumerator_shift as y).symm
        have htail :=
          (ih (N := y) hy_pos hy_odd harest).mpr ⟨m, hm, htailEq⟩
        exact ⟨hhead, by simpa [hy_step] using htail⟩

/-- Finite-function adapter for the list-inductive characterization. -/
theorem syracuse_exact_valuation_prefix_fin_iff
    (N t : ℕ) (hN : 0 < N) (hodd : Odd N)
    (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    syracuseExactValuationPrefix N (List.ofFn a) ↔
      ∃ m : ℕ, Odd m ∧
        2 ^ (∑ i, a i) * m = syracuseAffineNumerator (List.ofFn a) N := by
  have hlist : ∀ b ∈ List.ofFn a, 0 < b := by
    rw [List.forall_mem_ofFn_iff]
    exact ha
  have h := syracuse_exact_valuation_prefix_iff N hN hodd (List.ofFn a) hlist
  simpa [List.sum_ofFn] using h





set_option autoImplicit false

open Nat
open scoped BigOperators

/- An odd quotient is exactly the residue `2^S` modulo the next power of two. -/
theorem odd_quotient_iff_modEq_pow_two (A S : ℕ) :
    (∃ m : ℕ, Odd m ∧ 2 ^ S * m = A) ↔
      Nat.ModEq (2 ^ (S + 1)) A (2 ^ S) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨q, hq⟩ := hm
    rw [hq]
    have hle : 2 ^ S ≤ 2 ^ S * (2 * q + 1) := by
      have hp : 0 < 2 ^ S := Nat.pow_pos (by decide)
      nlinarith
    have hdvd : 2 ^ (S + 1) ∣ 2 ^ S * (2 * q + 1) - 2 ^ S := by
      refine ⟨q, ?_⟩
      rw [pow_succ]
      ring_nf
      omega
    exact (Nat.modEq_iff_dvd' hle).mpr hdvd |>.symm
  · intro h
    have hpow : 2 ^ S < 2 ^ (S + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ S := Nat.pow_pos (by decide)
      omega
    have hrem : A % 2 ^ (S + 1) = 2 ^ S := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hpow] using h
    have hdecomp := Nat.mod_add_div A (2 ^ (S + 1))
    refine ⟨2 * (A / 2 ^ (S + 1)) + 1, ?_, ?_⟩
    · exact ⟨A / 2 ^ (S + 1), by omega⟩
    · rw [hrem] at hdecomp
      calc
        2 ^ S * (2 * (A / 2 ^ (S + 1)) + 1) =
            2 ^ S + 2 ^ (S + 1) * (A / 2 ^ (S + 1)) := by
              rw [pow_succ]
              ring
        _ = A := hdecomp

private lemma syracuse_affine_coefficient_coprime (t S : ℕ) :
    Nat.Coprime (2 ^ (S + 1)) (3 ^ t) := by
  exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)

private lemma affine_residue_exists (t S C : ℕ) :
    ∃ r : Fin (2 ^ (S + 1)),
      Nat.ModEq (2 ^ (S + 1)) (3 ^ t * r.val + C) (2 ^ S) := by
  let M : ℕ := 2 ^ (S + 1)
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  haveI : NeZero M := ⟨hM.ne'⟩
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime (3 ^ t)
    (by simpa [M] using (syracuse_affine_coefficient_coprime t S).symm)
  let z : ZMod M := (u⁻¹ : ZMod M) * ((2 ^ S : ZMod M) - (C : ZMod M))
  let r : Fin M := ⟨z.val, ZMod.val_lt z⟩
  refine ⟨r, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ M).mp
  dsimp [r, z]
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hu : (u : ZMod M) = 3 ^ t := by
    simp [u]
  have hu' : ((3 ^ t : ℕ) : ZMod M) = (u : ZMod M) := by simpa using hu.symm
  rw [hu']
  simp

private lemma affine_modEq_iff_residue
    (t S C : ℕ) (r : Fin (2 ^ (S + 1)))
    (hr : Nat.ModEq (2 ^ (S + 1)) (3 ^ t * r.val + C) (2 ^ S))
    (N : ℕ) :
    Nat.ModEq (2 ^ (S + 1)) (3 ^ t * N + C) (2 ^ S) ↔
      N % 2 ^ (S + 1) = r.val := by
  have hcop : Nat.Coprime (2 ^ (S + 1)) (3 ^ t) :=
    syracuse_affine_coefficient_coprime t S
  constructor
  · intro hN
    have hmul : Nat.ModEq (2 ^ (S + 1)) (3 ^ t * N) (3 ^ t * r.val) := by
      exact Nat.ModEq.add_right_cancel' C (hN.trans hr.symm)
    have hcancel := Nat.ModEq.cancel_left_of_coprime hcop hmul
    simpa [Nat.ModEq, Nat.mod_eq_of_lt r.isLt] using hcancel
  · intro hN
    have hNr : Nat.ModEq (2 ^ (S + 1)) N r.val := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt r.isLt] using hN
    exact (Nat.ModEq.mul_left (3 ^ t) hNr).add_right C |>.trans hr

private lemma affine_constant_odd_of_pos
    (as : List ℕ) (hpos : ∀ b ∈ as, 0 < b) (hne : as ≠ []) :
    Odd (syracuseAffineConstant as) := by
  cases as with
  | nil => contradiction
  | cons b bs =>
      exact syracuseAffineConstant_cons_odd b bs (hpos b (by simp))

theorem syracuse_exact_prefix_residue
    (t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      ∀ N : ℕ, 0 < N → Odd N →
        (syracuseExactValuationPrefix N (List.ofFn a) ↔
          N % 2 ^ ((∑ i, a i) + 1) = r.val) := by
  by_cases ht : t = 0
  · subst t
    have hsum : ∑ i, a i = 0 := by simp
    have hrbound : 1 < 2 ^ ((∑ i, a i) + 1) := by
      rw [hsum]
      decide
    let r : Fin (2 ^ ((∑ i, a i) + 1)) := ⟨1, hrbound⟩
    refine ⟨r, ?_, ?_⟩
    · change Odd 1
      exact ⟨0, by omega⟩
    · exact fun N hN hodd ↦ by
        constructor
        · intro _
          obtain ⟨k, hk⟩ := hodd
          simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_add, pow_one] at *
          simp [r, hk]
        · intro _
          trivial
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    let S : ℕ := ∑ i, a i
    let C : ℕ := syracuseAffineConstant (List.ofFn a)
    obtain ⟨r, hr⟩ := affine_residue_exists t S C
    have hS : 0 < S := by
      dsimp [S]
      exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨⟨0, htpos⟩, Finset.mem_univ _, ha _⟩
    have hCodd : Odd C := by
      have hposlist : ∀ b ∈ List.ofFn a, 0 < b := by
        rw [List.forall_mem_ofFn_iff]
        exact ha
      have hne : (List.ofFn a).length ≠ 0 := by simp [ht]
      have hne' : List.ofFn a ≠ [] := by simpa using hne
      dsimp [C]
      exact affine_constant_odd_of_pos (List.ofFn a) hposlist hne'
    have hrodd : Odd r.val := by
      obtain ⟨m, hm, hEq⟩ :=
        (odd_quotient_iff_modEq_pow_two (3 ^ t * r.val + C) S).mpr hr
      have hEven : Even (3 ^ t * r.val + C) := by
        rw [← hEq]
        exact ((show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
          (by omega : S ≠ 0)).mul_right m
      have hprod : Odd (3 ^ t * r.val) := (even_add').mp hEven |>.mpr hCodd
      exact hprod.of_mul_right
    refine ⟨r, hrodd, ?_⟩
    exact fun N hN hodd ↦ by
      have hprefix :
          syracuseExactValuationPrefix N (List.ofFn a) ↔
            ∃ m : ℕ, Odd m ∧ 2 ^ S * m = 3 ^ t * N + C := by
        rw [syracuse_exact_valuation_prefix_fin_iff N t hN hodd a ha]
        simp [S, C, syracuseAffineNumerator, List.length_ofFn]
      rw [hprefix, odd_quotient_iff_modEq_pow_two]
      exact affine_modEq_iff_residue t S C r hr N





set_option autoImplicit false

open Nat

/- The recursive list predicate from the affine-prefix proof is exactly the
   coordinate-wise assertion on the corresponding finite tuple. -/
theorem syracuse_exact_prefix_coordinates
    (N t : ℕ) (a : Fin t → ℕ) (hN : 0 < N) (hodd : Odd N)
    (ha : ∀ i, 0 < a i) :
    syracuseExactValuationPrefix N (List.ofFn a) ↔
      ∀ i : Fin t, syracuseExponent N i = a i := by
  induction t generalizing N with
  | zero =>
      simp [syracuseExactValuationPrefix]
  | succ t ih =>
      let tail : Fin t → ℕ := fun i => a i.succ
      have htail_pos : ∀ i, 0 < tail i := by
        intro i
        exact ha i.succ
      have haeq : a = Fin.cons (a 0) tail := by
        funext i
        exact Fin.cases rfl (fun j => rfl) i
      rw [haeq, List.ofFn_cons]
      have hstep_pos : 0 < syracuseStep N := syracuse_step_pos hN
      have hstep_odd : Odd (syracuseStep N) := syracuse_step_odd hN
      have ihstep :
          syracuseExactValuationPrefix (syracuseStep N) (List.ofFn tail) ↔
            ∀ i : Fin t, syracuseExponent (syracuseStep N) i = tail i :=
        ih (N := syracuseStep N) (a := tail) hstep_pos hstep_odd htail_pos
      constructor
      · rintro ⟨hhead, htail⟩ i
        refine Fin.cases hhead (fun j => ?_) i
        have hj' := (ihstep.mp htail) j
        rw [syracuse_exponent_step_shift] at hj'
        exact hj'
      · intro hcoords
        refine ⟨hcoords 0, ?_⟩
        apply ihstep.mpr
        intro j
        have hj := hcoords j.succ
        rw [syracuse_exponent_step_shift]
        simpa using hj

theorem syracuse_exact_prefix_coordinates_residue
    (t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      ∀ N : ℕ, 0 < N → Odd N →
        ((∀ i : Fin t, syracuseExponent N i = a i) ↔
          N % 2 ^ ((∑ i, a i) + 1) = r.val) := by
  obtain ⟨r, hr, hres⟩ := syracuse_exact_prefix_residue t a ha
  refine ⟨r, hr, ?_⟩
  intro N hN hodd
  rw [← syracuse_exact_prefix_coordinates N t a hN hodd ha]
  exact hres N hN hodd




set_option autoImplicit false

/-- A fixed residue occurs exactly `n` times in a complete interval of length `m*n`. -/
theorem finite_mod_fiber_card (m n r : ℕ) (hm : 0 < m) (hr : r < m) :
    Fintype.card {x : Fin (m * n) // x.val % m = r} = n := by
  let e : {x : Fin (m * n) // x.val % m = r} ≃ Fin n :=
    { toFun := fun x => ⟨x.val.val / m, by
        apply (Nat.div_lt_iff_lt_mul hm).mpr
        simpa [Nat.mul_comm] using x.val.isLt⟩
      invFun := fun k => ⟨⟨r + m * k.val, by
        have hk : k.val + 1 ≤ n := k.isLt
        calc
          r + m * k.val < m + m * k.val := Nat.add_lt_add_right hr _
          _ = m * (k.val + 1) := by ring
          _ ≤ m * n := Nat.mul_le_mul_left m hk⟩, by
            simp [Nat.add_mod, Nat.mod_eq_of_lt hr]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Fin.ext
        change r + m * (x.val.val / m) = x.val.val
        exact (congrArg (fun z => z + m * (x.val.val / m)) x.property.symm).trans
          (Nat.mod_add_div _ _)
      right_inv := by
        intro k
        apply Fin.ext
        change (r + m * k.val) / m = k.val
        rw [Nat.add_mul_div_left _ _ hm]
        simp [Nat.div_eq_of_lt hr] }
  simpa using Fintype.card_congr e

/-- The exact number of lifts of a residue through a power-of-two modulus. -/
theorem power_two_mod_fiber_card (q s r : ℕ) (hs : s ≤ q) (hr : r < 2 ^ s) :
    Fintype.card {x : Fin (2 ^ q) // x.val % 2 ^ s = r} = 2 ^ (q - s) := by
  have hprod : 2 ^ q = 2 ^ s * 2 ^ (q - s) := by
    rw [← pow_add, Nat.add_sub_of_le hs]
  rw [hprod]
  exact finite_mod_fiber_card _ _ _ (Nat.pow_pos (by decide)) hr





set_option autoImplicit false

open Nat
open scoped BigOperators

private lemma positive_of_mod_eq {M r x : ℕ} (hr : 0 < r)
    (hmod : x % M = r) : 0 < x := by
  by_contra hx
  have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
  subst x
  simp at hmod
  omega

private lemma positive_of_odd {r : ℕ} (hr : Odd r) : 0 < r := by
  obtain ⟨k, hk⟩ := hr
  omega

private lemma odd_of_mod_eq_pow_two {s r x : ℕ} (hr : Odd r)
    (hmod : x % 2 ^ (s + 1) = r) : Odd x := by
  have hpow_even : Even (2 ^ (s + 1)) := by
    exact (show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero (by omega)
  have hprod_even : Even (2 ^ (s + 1) * (x / 2 ^ (s + 1))) :=
    hpow_even.mul_right _
  have hdecomp := Nat.mod_add_div x (2 ^ (s + 1))
  rw [hmod] at hdecomp
  rw [← hdecomp]
  exact hr.add_even hprod_even

theorem syracuse_exact_prefix_finite_card
    (q t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i)
    (hSq : (∑ i, a i) < q) :
    Fintype.card {x : Fin (2 ^ q) //
        0 < x.val ∧ Odd x.val ∧
          ∀ i : Fin t, syracuseExponent x.val i = a i} =
      2 ^ (q - ((∑ i, a i) + 1)) := by
  let S : ℕ := ∑ i, a i
  let M : ℕ := 2 ^ (S + 1)
  have hSM : S + 1 ≤ q := by
    dsimp [S]
    omega
  obtain ⟨r, hrOdd, hres⟩ := syracuse_exact_prefix_coordinates_residue t a ha
  have hrpos : 0 < r.val := positive_of_odd hrOdd
  let E : Type := {x : Fin (2 ^ q) //
    0 < x.val ∧ Odd x.val ∧ ∀ i : Fin t, syracuseExponent x.val i = a i}
  let F : Type := {x : Fin (2 ^ q) // x.val % M = r.val}
  let e : E ≃ F :=
    { toFun := fun x =>
        ⟨x.1, by
          dsimp [M]
          exact (hres x.1.val x.2.1 x.2.2.1).mp x.2.2.2⟩
      invFun := fun x =>
        ⟨x.1, by
          have hxpos : 0 < x.1.val := positive_of_mod_eq hrpos (by simpa [M] using x.2)
          have hxodd : Odd x.1.val := odd_of_mod_eq_pow_two hrOdd (by simpa [M] using x.2)
          exact ⟨hxpos, hxodd, (hres x.1.val hxpos hxodd).mpr (by simpa [M] using x.2)⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  have hcardEF : Fintype.card E = Fintype.card F := Fintype.card_congr e
  have hcardF : Fintype.card F = 2 ^ (q - (S + 1)) := by
    dsimp [F, M]
    exact power_two_mod_fiber_card q (S + 1) r.val hSM r.isLt
  simpa [E, S] using hcardEF.trans hcardF

theorem syracuse_exact_prefix_finite_card_normalized
    (q t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i)
    (hSq : (∑ i, a i) < q) :
    (Fintype.card {x : Fin (2 ^ q) //
        0 < x.val ∧ Odd x.val ∧
          ∀ i : Fin t, syracuseExponent x.val i = a i} : ℝ) /
        (2 ^ (q - 1) : ℝ) =
      1 / (2 ^ (∑ i, a i) : ℝ) := by
  let S : ℕ := ∑ i, a i
  have hcard := syracuse_exact_prefix_finite_card q t a ha hSq
  have hS1 : S + 1 ≤ q := by
    dsimp [S]
    omega
  have hqsplit : q - 1 = S + (q - (S + 1)) := by omega
  rw [hcard]
  rw [hqsplit, pow_add]
  field_simp
  simp [Nat.cast_pow, S, mul_comm]


/-- Bounded positive exponent prefixes used by the finite good set. -/
def PositiveExponentPrefix (k n' : ℕ) :=
  {a : Fin k → Fin n' // (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}

instance positiveExponentPrefixFintype (k n' : ℕ) :
    Fintype (PositiveExponentPrefix k n') := by
  classical
  unfold PositiveExponentPrefix
  infer_instance


set_option autoImplicit false

open Nat
open scoped BigOperators

def positiveExponentPrefixValues {t q : ℕ}
    (a : PositiveExponentPrefix t q) : Fin t → ℕ :=
  fun i => (a.1 i).val

noncomputable def shortPositiveVectorFinset (t q : ℕ) : Finset (Fin t → ℕ) := by
  classical
  exact (Finset.univ : Finset (PositiveExponentPrefix t q)).image
    positiveExponentPrefixValues

theorem positiveExponentPrefixValues_injective (t q : ℕ) :
    Function.Injective (positiveExponentPrefixValues :
      PositiveExponentPrefix t q → (Fin t → ℕ)) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun hab i

theorem mem_shortPositiveVectorFinset_iff
    (t q : ℕ) (a : Fin t → ℕ) :
    a ∈ shortPositiveVectorFinset t q ↔
      (∀ i, 0 < a i) ∧ (∑ i, a i) < q := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨b, -, rfl⟩
    exact b.2
  · rintro ⟨ha, hsum⟩
    have hai : ∀ i, a i < q := by
      intro i
      have hle : a i ≤ ∑ j, a j :=
        Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    let b : PositiveExponentPrefix t q :=
      ⟨fun i => ⟨a i, hai i⟩, ha, hsum⟩
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_univ _, ?_⟩
    funext i
    rfl

theorem sum_over_shortPositiveVectorFinset
    (t q : ℕ) (f : (Fin t → ℕ) → ℝ) :
    ∑ a ∈ shortPositiveVectorFinset t q, f a =
      ∑ a : PositiveExponentPrefix t q, f (positiveExponentPrefixValues a) := by
  classical
  unfold shortPositiveVectorFinset
  rw [Finset.sum_image]
  exact (positiveExponentPrefixValues_injective t q).injOn





set_option autoImplicit false

open Nat
open scoped BigOperators

noncomputable def syracuseShortPrefixEvent
    (q t : ℕ) (a : Fin t → ℕ) : Finset (Fin (2 ^ q)) := by
  classical
  exact Finset.univ.filter (fun x =>
    0 < x.val ∧ Odd x.val ∧ ∀ i : Fin t, syracuseExponent x.val i = a i)

noncomputable def syracuseShortPrefixResidue (q N : ℕ) : Fin (2 ^ q) :=
  ⟨N % 2 ^ q, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

private lemma positive_of_mod_eq_short {M r x : ℕ} (hr : 0 < r)
    (hmod : x % M = r) : 0 < x := by
  by_contra hx
  have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
  subst x
  simp at hmod
  omega

private lemma positive_of_odd_short {r : ℕ} (hr : Odd r) : 0 < r := by
  obtain ⟨k, hk⟩ := hr
  omega

private lemma odd_of_mod_eq_pow_two_short {s r x : ℕ} (hr : Odd r)
    (hmod : x % 2 ^ (s + 1) = r) : Odd x := by
  have hpow_even : Even (2 ^ (s + 1)) := by
    exact (show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero (by omega)
  have hprod_even : Even (2 ^ (s + 1) * (x / 2 ^ (s + 1))) :=
    hpow_even.mul_right _
  have hdecomp := Nat.mod_add_div x (2 ^ (s + 1))
  rw [hmod] at hdecomp
  rw [← hdecomp]
  exact hr.add_even hprod_even

private lemma pow_sub_divides_pow_short (S q : ℕ) (hS : S + 1 ≤ q) :
    2 ^ (S + 1) ∣ 2 ^ q := by
  refine ⟨2 ^ (q - (S + 1)), ?_⟩
  rw [← pow_add, Nat.add_sub_of_le hS]

theorem syracuse_short_prefix_event_mem_iff
    (q t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i)
    (hSq : (∑ i, a i) < q) (N : ℕ) (hN : 0 < N) (hodd : Odd N) :
    (∀ i : Fin t, syracuseExponent N i = a i) ↔
      syracuseShortPrefixResidue q N ∈ syracuseShortPrefixEvent q t a := by
  classical
  let S : ℕ := ∑ i, a i
  have hSM : S + 1 ≤ q := by
    dsimp [S]
    omega
  obtain ⟨r, hrOdd, hres⟩ := syracuse_exact_prefix_coordinates_residue t a ha
  have hrpos : 0 < r.val := positive_of_odd_short hrOdd
  have hdiv : 2 ^ (S + 1) ∣ 2 ^ q := pow_sub_divides_pow_short S q hSM
  have hresidue_mod (x : ℕ) (hx : x = N % 2 ^ q) :
      x % 2 ^ (S + 1) = r.val ↔
        N % 2 ^ (S + 1) = r.val := by
    subst x
    rw [Nat.mod_mod_of_dvd N hdiv]
  constructor
  · intro hcoords
    have hsmall : N % 2 ^ (S + 1) = r.val := (hres N hN hodd).mp hcoords
    have hmod : (N % 2 ^ q) % 2 ^ (S + 1) = r.val := by
      exact (hresidue_mod (N % 2 ^ q) rfl).mpr hsmall
    have hxpos : 0 < (N % 2 ^ q) := positive_of_mod_eq_short hrpos hmod
    have hxodd : Odd (N % 2 ^ q) := odd_of_mod_eq_pow_two_short hrOdd hmod
    have hxcoords : ∀ i : Fin t, syracuseExponent (N % 2 ^ q) i = a i := by
      exact (hres (N % 2 ^ q) hxpos hxodd).mpr hmod
    change syracuseShortPrefixResidue q N ∈
      Finset.univ.filter (fun x =>
        0 < x.val ∧ Odd x.val ∧
          ∀ i : Fin t, syracuseExponent x.val i = a i)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change 0 < N % 2 ^ q ∧ Odd (N % 2 ^ q) ∧
      ∀ i : Fin t, syracuseExponent (N % 2 ^ q) i = a i
    exact ⟨hxpos, hxodd, hxcoords⟩
  · intro hmem
    have hmem' := (Finset.mem_filter.mp hmem).2
    have hxpos : 0 < (N % 2 ^ q) := hmem'.1
    have hxodd : Odd (N % 2 ^ q) := hmem'.2.1
    have hxcoords := hmem'.2.2
    have hsmall : (N % 2 ^ q) % 2 ^ (S + 1) = r.val :=
      (hres (N % 2 ^ q) hxpos hxodd).mp hxcoords
    have hsmallN : N % 2 ^ (S + 1) = r.val :=
      (hresidue_mod (N % 2 ^ q) rfl).mp hsmall
    exact (hres N hN hodd).mpr hsmallN

theorem syracuse_short_prefix_events_pairwise_disjoint
    (q t : ℕ) (a b : PositiveExponentPrefix t q) (hab : a ≠ b) :
    Disjoint (syracuseShortPrefixEvent q t (fun i => (a.1 i).val))
      (syracuseShortPrefixEvent q t (fun i => (b.1 i).val)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hxa' := (Finset.mem_filter.mp hxa).2.2.2
  have hxb' := (Finset.mem_filter.mp hxb).2.2.2
  apply hab
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact (hxa' i).symm.trans (hxb' i)



/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open MeasureTheory
open Set
open scoped BigOperators

set_option autoImplicit false

/-!
# Finite-valued law events are sums of atom masses

For a measurable random variable with finite-valued codomain, the real mass of
an event selecting finitely many values is the sum of the real masses of its
singleton fibers.  The measurable-singleton assumption is explicit because a
bare finite measurable space need not contain every singleton as measurable.
-/

theorem finite_law_event_mass_eq_sum_atoms
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (E : Finset α) (hX : Measurable X) :
    (μ (X ⁻¹' (E : Set α))).toReal =
      ∑ a ∈ E, (μ (X ⁻¹' ({a} : Set α))).toReal := by
  exact (sum_measureReal_preimage_singleton E
    (fun a ha => hX (MeasurableSet.singleton a))).symm



/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open scoped BigOperators

set_option autoImplicit false

/-!
# Finite L1 control on disjoint events

For a finite pairwise-disjoint family of source events, the sum of the
absolute discrepancies of their aggregate masses is bounded by the source
L1 discrepancy.  The inputs are arbitrary real functions; no positivity or
normalization is needed.
-/

open scoped Classical in
theorem finite_l1_disjoint_events
    {α ι : Type*} [Fintype α] [Fintype ι]
    (E : ι → Finset α) (p g : α → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    (∑ i : ι, |∑ a ∈ E i, (p a - g a)|) ≤
      ∑ a : α, |p a - g a| := by
  have hdisj' : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint E := by
    intro i hi j hj hij
    exact hdisj hij
  calc
    (∑ i : ι, |∑ a ∈ E i, (p a - g a)|) ≤
        ∑ i : ι, ∑ a ∈ E i, |p a - g a| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ (Finset.univ : Finset ι).biUnion E, |p a - g a| := by
      symm
      simpa using (Finset.sum_biUnion (s := (Finset.univ : Finset ι))
        (t := E) hdisj')
    _ ≤ ∑ a : α, |p a - g a| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ((Finset.univ : Finset ι).biUnion E))
      intro a ha hnot
      exact abs_nonneg _



/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open MeasureTheory
open Set
open scoped BigOperators

set_option autoImplicit false

/-!
# Finite-valued law discrepancies on disjoint events

The real mass discrepancy of a finite pairwise-disjoint family of measurable
events is bounded by the atomwise L1 discrepancy of the underlying finite law.
This consumer combines the finite-event mass identity with the static disjoint
event contraction.
-/

open scoped Classical in
theorem finite_law_disjoint_l1
    {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (E : ι → Finset α) (g : α → ℝ)
    (hX : Measurable X)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) :
    (∑ i : ι,
        |(μ (X ⁻¹' (E i : Set α))).toReal - ∑ a ∈ E i, g a|) ≤
      ∑ a : α, |(μ (X ⁻¹' ({a} : Set α))).toReal - g a| := by
  let p : α → ℝ := fun a => (μ (X ⁻¹' ({a} : Set α))).toReal
  have hmass (i : ι) :
      (μ (X ⁻¹' (E i : Set α))).toReal = ∑ a ∈ E i, p a := by
    exact finite_law_event_mass_eq_sum_atoms μ X (E i) hX
  calc
    (∑ i : ι,
        |(μ (X ⁻¹' (E i : Set α))).toReal - ∑ a ∈ E i, g a|) =
        ∑ i : ι, |(∑ a ∈ E i, p a) - ∑ a ∈ E i, g a| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmass i]
    _ = ∑ i : ι, |∑ a ∈ E i, (p a - g a)| := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a : α, |p a - g a| :=
      finite_l1_disjoint_events E p g hdisj
    _ = ∑ a : α, |(μ (X ⁻¹' ({a} : Set α))).toReal - g a| := by
      rfl




set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

/-- The singleton fibers of a countable-valued random variable have total mass one. -/
theorem countable_law_atoms_tsum
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    (∑' a : α, μ (X ⁻¹' ({a} : Set α))) = 1 := by
  have h := tsum_measure_preimage_singleton (μ := μ)
    (s := Set.univ) (Set.to_countable _) (f := X)
    (fun a _ => hX (MeasurableSet.singleton a))
  calc
    (∑' a : α, μ (X ⁻¹' ({a} : Set α))) =
        ∑' a : (Set.univ : Set α), μ (X ⁻¹' ({a.val} : Set α)) :=
      (tsum_univ (fun a : α => μ (X ⁻¹' ({a} : Set α)))).symm
    _ = 1 := by simpa only [Set.preimage_univ, measure_univ] using h

/-- Countable atom masses are summable as real numbers; no finite support is assumed. -/
theorem countable_law_atoms_summable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    Summable (fun a : α => (μ (X ⁻¹' ({a} : Set α))).toReal) := by
  apply ENNReal.summable_toReal
  rw [countable_law_atoms_tsum μ X hX]
  exact ENNReal.one_ne_top

/-- The real atom masses of a countable-valued probability law sum to one. -/
theorem countable_law_atoms_real_tsum
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    (∑' a : α, (μ (X ⁻¹' ({a} : Set α))).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => measure_ne_top μ _),
    countable_law_atoms_tsum μ X hX, ENNReal.toReal_one]

/-- A countable event has real mass equal to the sum of its atom masses. -/
theorem countable_law_event_real_tsum
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (E : Set α) :
    (∑' a : E, (μ (X ⁻¹' ({a.val} : Set α))).toReal) =
      (μ (X ⁻¹' E)).toReal := by
  rw [← ENNReal.tsum_toReal_eq (fun a => measure_ne_top μ _)]
  exact congrArg ENNReal.toReal
    (tsum_measure_preimage_singleton (μ := μ) (Set.to_countable E)
      (fun a _ => hX (MeasurableSet.singleton a)))



/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open scoped BigOperators

set_option autoImplicit false

/-!
# Static countable total-variation splitting

For nonnegative summable functions `p` and `g`, a finite set `F` separates the
total `ℓ¹` discrepancy into its finite discrepancy and the two complementary
masses.  This is a static decomposition; it contains no limiting or
quantitative-in-parameter assertion.
-/

theorem tsum_abs_sub_le_finset_add_tsum_compl
    {α : Type*} [Countable α]
    (p g : α → ℝ) (F : Finset α)
    (hp : Summable p) (hg : Summable g)
    (hpg : Summable (fun a => |p a - g a|))
    (hp_nonneg : ∀ a, 0 ≤ p a) (hg_nonneg : ∀ a, 0 ≤ g a) :
    (∑' a, |p a - g a|) ≤
      (∑ a ∈ F, |p a - g a|) +
        (∑' a : {a // a ∉ F}, p a) +
        (∑' a : {a // a ∉ F}, g a) := by
  have hpoint : ∀ a : {a // a ∉ F}, |p a - g a| ≤ p a + g a := by
    intro a
    rw [abs_sub_le_iff]
    constructor <;> linarith [hp_nonneg a, hg_nonneg a]
  have hp_compl : Summable (fun a : {a // a ∉ F} => p a) := hp.subtype _
  have hg_compl : Summable (fun a : {a // a ∉ F} => g a) := hg.subtype _
  have hpg_compl : Summable (fun a : {a // a ∉ F} => |p a - g a|) :=
    hpg.subtype _
  have hsum_compl :
      (∑' a : {a // a ∉ F}, |p a - g a|) ≤
        (∑' a : {a // a ∉ F}, p a) + (∑' a : {a // a ∉ F}, g a) := by
    rw [← hp_compl.tsum_add hg_compl]
    exact hpg_compl.tsum_le_tsum hpoint (hp_compl.add hg_compl)
  calc
    (∑' a, |p a - g a|) =
        (∑ a ∈ F, |p a - g a|) +
          (∑' a : {a // a ∉ F}, |p a - g a|) :=
      (hpg.sum_add_tsum_compl (s := F)).symm
    _ ≤ (∑ a ∈ F, |p a - g a|) +
        (∑' a : {a // a ∉ F}, p a) +
        (∑' a : {a // a ∉ F}, g a) := by
          simpa [add_assoc, add_comm, add_left_comm] using
            (add_le_add_right hsum_compl (∑ a ∈ F, |p a - g a|))



/-
  One-tail reduction for countable total variation.

  If two nonnegative summable laws have total mass one, a finite-set
  discrepancy controls the full `ℓ¹` discrepancy up to twice the reference
  law's complementary mass.  This is the static finite-good-set estimate used
  by the Tao-shaped assembly; it does not assert any limiting law.
-/


open scoped BigOperators

set_option autoImplicit false

theorem tsum_abs_sub_le_two_mul_finset_add_two_mul_compl
    {α : Type*} [Countable α]
    (p g : α → ℝ) (F : Finset α)
    (hp : Summable p) (hg : Summable g)
    (hp_total : (∑' a, p a) = 1) (hg_total : (∑' a, g a) = 1)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hg_nonneg : ∀ a, 0 ≤ g a) :
    (∑' a, |p a - g a|) ≤
      2 * (∑ a ∈ F, |p a - g a|) +
        2 * (∑' a : {a // a ∉ F}, p a) := by
  have hpoint : ∀ a, |p a - g a| ≤ p a + g a := by
    intro a
    rw [abs_sub_le_iff]
    constructor <;> linarith [hp_nonneg a, hg_nonneg a]
  have hpg : Summable (fun a => |p a - g a|) :=
    Summable.of_nonneg_of_le (fun a => abs_nonneg _) hpoint (hp.add hg)
  have hsplit := tsum_abs_sub_le_finset_add_tsum_compl
    p g F hp hg hpg hp_nonneg hg_nonneg
  have hp_split := hp.sum_add_tsum_compl (s := F)
  have hg_split := hg.sum_add_tsum_compl (s := F)
  let e : {a // a ∉ F} ≃ {a // a ∈ (↑(F : Finset α) : Set α)ᶜ} :=
    { toFun := fun a => ⟨a.1, by simpa using a.2⟩
      invFun := fun a => ⟨a.1, by
        change a.1 ∉ (↑(F : Finset α) : Set α)
        exact a.2⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  have hp_compl_eq :
      (∑' a : {a // a ∉ F}, p a) =
        ∑' a : {a // a ∈ (↑(F : Finset α) : Set α)ᶜ}, p a := by
    simpa [e] using (e.tsum_eq (fun a => p a))
  have hg_compl_eq :
      (∑' a : {a // a ∉ F}, g a) =
        ∑' a : {a // a ∈ (↑(F : Finset α) : Set α)ᶜ}, g a := by
    simpa [e] using (e.tsum_eq (fun a => g a))
  have hp_split' :
      (∑ a ∈ F, p a) + (∑' a : {a // a ∉ F}, p a) = ∑' a, p a := by
    rw [hp_compl_eq]
    exact hp_split
  have hg_split' :
      (∑ a ∈ F, g a) + (∑' a : {a // a ∉ F}, g a) = ∑' a, g a := by
    rw [hg_compl_eq]
    exact hg_split
  have hfinite :
      |(∑ a ∈ F, p a) - ∑ a ∈ F, g a| ≤
        ∑ a ∈ F, |p a - g a| := by
    simpa [Finset.sum_sub_distrib] using
      (Finset.abs_sum_le_sum_abs (fun a => p a - g a) F)
  have hcomp :
      (∑' a : {a // a ∉ F}, g a) ≤
        (∑' a : {a // a ∉ F}, p a) +
          (∑ a ∈ F, |p a - g a|) := by
    have hfinite' :
        (∑ a ∈ F, p a) - ∑ a ∈ F, g a ≤
          ∑ a ∈ F, |p a - g a| :=
      (le_abs_self _).trans hfinite
    linarith [hp_split', hg_split', hfinite', hp_total, hg_total]
  linarith [hsplit, hcomp]



/-
  Verified model and atom formulas for the positive-support geometric vector used
  by the Tao-shaped valuation tail.  The finite tail identity is not asserted here:
  its finite composition-fiber reduction remains the next proof stage.

  Mathlib's geometric measure counts failures before the first success, so its
  support is zero-based.  The definition below shifts it by `Nat.succ`; it
  therefore has mass `2⁻ᵏ` at positive `k`.
-/


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal unitInterval

noncomputable section

private def geomTwoParam : unitInterval :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

private lemma geomTwoParam_ne_zero : geomTwoParam ≠ 0 := by
  intro h
  have h' := congrArg (fun x : unitInterval => (x : ℝ)) h
  norm_num [geomTwoParam] at h'

/-- The positive-support `Geom(2)` law, obtained by shifting Mathlib's law. -/
def positiveGeomTwo : Measure ℕ :=
  (geometricMeasure geomTwoParam).map Nat.succ

instance positiveGeomTwo_isProbabilityMeasure : IsProbabilityMeasure positiveGeomTwo :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- A finite independent vector of positive-support `Geom(2)` variables. -/
def positiveGeomTwoVector (t : ℕ) : Measure (Fin t → ℕ) :=
  Measure.pi (fun _ : Fin t => positiveGeomTwo)

/-- The sum of a positive geometric vector. -/
def positiveGeomTwoSum (t : ℕ) (a : Fin t → ℕ) : ℕ :=
  ∑ i, a i

lemma positiveGeomTwo_real_singleton (n : ℕ) :
    positiveGeomTwo.real {n + 1} = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [positiveGeomTwo, map_measureReal_apply (by fun_prop) (by measurability)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by
    ext x
    simp [Nat.succ_eq_add_one]
  rw [hpre]
  have h := geometricMeasure_real_singleton (p := geomTwoParam) geomTwoParam_ne_zero n
  rw [show (geomTwoParam : ℝ) = 1 / 2 by rfl] at h
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num] at h
  simpa [pow_succ] using h

lemma positiveGeomTwo_singleton_zero : positiveGeomTwo {0} = 0 := by
  rw [positiveGeomTwo, Measure.map_apply (by fun_prop) (by measurability)]
  have hpre : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by
    ext x
    simp
  rw [hpre]
  simp

lemma positiveGeomTwo_singleton_succ (n : ℕ) :
    positiveGeomTwo {n + 1} = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  rw [positiveGeomTwo, Measure.map_apply (by fun_prop) (by measurability)]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by
    ext x
    simp [Nat.succ_eq_add_one]
  rw [hpre]
  have h := geometricMeasure_singleton (p := geomTwoParam) geomTwoParam_ne_zero n
  rw [show (geomTwoParam : ℝ) = 1 / 2 by rfl] at h
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num] at h
  simpa [pow_succ] using h

lemma positiveGeomTwoVector_real_singleton (t : ℕ) (a : Fin t → ℕ) :
    (positiveGeomTwoVector t).real {a} =
      if _ : ∀ i, 0 < a i then ∏ i, (1 / 2 : ℝ) ^ (a i) else 0 := by
  rw [positiveGeomTwoVector, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  by_cases h : ∀ i, 0 < a i
  · simp_rw [show ∀ i : Fin t, positiveGeomTwo {a i} =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (a i)) by
      intro i
      obtain ⟨n, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (h i))
      rw [hi]
      simpa [Nat.succ_eq_add_one] using positiveGeomTwo_singleton_succ n]
    have hnonneg : ∀ i : Fin t, 0 ≤ (1 / 2 : ℝ) ^ (a i) := fun i =>
      pow_nonneg (by norm_num) _
    simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
    simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hzero : a i = 0 := by omega
    have hiAtom : positiveGeomTwo {a i} = 0 := by
      rw [hzero]
      exact positiveGeomTwo_singleton_zero
    have hiReal : (positiveGeomTwo {a i}).toReal = 0 := by rw [hiAtom]; simp
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hiReal]
    simp [h]




set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

instance positiveGeomTwoVector_isProbabilityMeasure (t : ℕ) :
    IsProbabilityMeasure (positiveGeomTwoVector t) := by
  unfold positiveGeomTwoVector
  infer_instance

/-- Positive vector atoms are exactly the normalized short-prefix counting weights. -/
theorem positiveGeomTwoVector_atom_of_pos
    (t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    (positiveGeomTwoVector t).real {a} = 1 / (2 : ℝ) ^ (∑ i, a i) := by
  rw [positiveGeomTwoVector_real_singleton]
  simp only [dif_pos ha]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [one_div_pow]

theorem positiveGeomTwoVector_atoms_summable (t : ℕ) :
    Summable (fun a : Fin t → ℕ => (positiveGeomTwoVector t).real {a}) := by
  simpa only [Set.preimage_id, measureReal_def] using
    countable_law_atoms_summable (positiveGeomTwoVector t) id measurable_id

theorem positiveGeomTwoVector_atoms_tsum (t : ℕ) :
    (∑' a : Fin t → ℕ, (positiveGeomTwoVector t).real {a}) = 1 := by
  simpa only [Set.preimage_id, measureReal_def] using
    countable_law_atoms_real_tsum (positiveGeomTwoVector t) id measurable_id





set_option autoImplicit false

open MeasureTheory
open Set
open Nat
open scoped BigOperators

def syracuseValuationVector {Ω : Type*} (t : ℕ) (N : Ω → ℕ) (ω : Ω) : Fin t → ℕ :=
  fun i => syracuseExponent (N ω) i

theorem measurable_syracuseValuationVector
    {Ω : Type*} [MeasurableSpace Ω] (t : ℕ) (N : Ω → ℕ)
    (hN : Measurable N) : Measurable (syracuseValuationVector t N) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_countable (fun n : ℕ => syracuseExponent n i)).comp hN

theorem measurable_syracuseValuationSum
    {Ω : Type*} [MeasurableSpace Ω] (t : ℕ) (N : Ω → ℕ)
    (hN : Measurable N) :
    Measurable (fun ω => ∑ i : Fin t, syracuseExponent (N ω) i) := by
  have hv := measurable_syracuseValuationVector t N hN
  fun_prop

theorem ae_shortPositiveVectorFinset_compl_iff_valuation_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (t q : ℕ) (N : Ω → ℕ) (hAE : ∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) :
    {ω | syracuseValuationVector t N ω ∉ shortPositiveVectorFinset t q} =ᵐ[μ]
      {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i} := by
  filter_upwards [hAE] with ω hω
  have hpos : ∀ i : Fin t, 0 < syracuseExponent (N ω) i := by
    intro i
    exact syracuse_exponent_pos (N ω) i hω.1 hω.2
  have hmem := mem_shortPositiveVectorFinset_iff t q (syracuseValuationVector t N ω)
  apply propext
  change (syracuseValuationVector t N ω ∉ shortPositiveVectorFinset t q) ↔
    q ≤ ∑ i : Fin t, syracuseExponent (N ω) i
  constructor
  · intro hnotmem
    by_contra hnotle
    have hlt : (∑ i : Fin t, syracuseExponent (N ω) i) < q :=
      Nat.lt_of_not_ge hnotle
    exact hnotmem (hmem.mpr ⟨hpos, hlt⟩)
  · intro h hmem'
    have hlt := (hmem.mp hmem').2
    have hlt' : (∑ i : Fin t, syracuseExponent (N ω) i) < q := by
      simpa [syracuseValuationVector] using hlt
    omega

theorem measureReal_shortPositiveVectorFinset_compl_eq_valuation_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (t q : ℕ) (N : Ω → ℕ) (hAE : ∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) :
    (μ {ω | syracuseValuationVector t N ω ∉ shortPositiveVectorFinset t q}).toReal =
      (μ {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i}).toReal := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  exact ae_shortPositiveVectorFinset_compl_iff_valuation_tail μ t q N hAE



/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

open MeasureTheory
open Set
open Nat
open scoped BigOperators

set_option autoImplicit false

/-!
# Syracuse short-prefix L1 discrepancy

The pairwise-disjoint short-prefix events contract the raw residue-law L1
error.  The identification with exponent-prefix events is only almost
everywhere, using the positive-odd support hypothesis; the model mass is
computed from the exact normalized prefix count.
-/

open scoped Classical in
theorem syracuse_short_prefix_l1
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N)
    (hAE : ∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω))
    (q t : ℕ) (hq : 0 < q) :
    (∑ a : PositiveExponentPrefix t q,
        |(μ {ω | ∀ i : Fin t, syracuseExponent (N ω) i = (a.1 i).val}).toReal -
          1 / (2 : ℝ) ^ (∑ i, (a.1 i).val)|) ≤
      ∑ r : Fin (2 ^ q),
        |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
          (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| := by
  let X : Ω → Fin (2 ^ q) := fun ω => syracuseShortPrefixResidue q (N ω)
  let E : PositiveExponentPrefix t q → Finset (Fin (2 ^ q)) :=
    fun a => syracuseShortPrefixEvent q t (fun i => (a.1 i).val)
  let g : Fin (2 ^ q) → ℝ :=
    fun r => if Odd r.val then 2 / (2 : ℝ) ^ q else 0
  have hX : Measurable X := by
    dsimp [X]
    have hres : Measurable (fun n : ℕ => syracuseShortPrefixResidue q n) :=
      measurable_of_countable _
    exact hres.comp hN
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    exact syracuse_short_prefix_events_pairwise_disjoint q t a b hab
  have hmass (a : PositiveExponentPrefix t q) :
      (μ (X ⁻¹' (E a : Set (Fin (2 ^ q))))).toReal =
        (μ {ω | ∀ i : Fin t, syracuseExponent (N ω) i = (a.1 i).val}).toReal := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hAE] with ω hω
    change (syracuseShortPrefixResidue q (N ω) ∈
      syracuseShortPrefixEvent q t (fun i => (a.1 i).val)) =
      (∀ i : Fin t, syracuseExponent (N ω) i = (a.1 i).val)
    exact propext (syracuse_short_prefix_event_mem_iff q t
      (fun i => (a.1 i).val) a.2.1 a.2.2 (N ω) hω.1 hω.2).symm
  have hmodel (a : PositiveExponentPrefix t q) :
      ∑ r ∈ E a, g r = 1 / (2 : ℝ) ^ (∑ i, (a.1 i).val) := by
    let av : Fin t → ℕ := fun i => (a.1 i).val
    have hav : ∀ i, 0 < av i := by
      intro i
      exact a.2.1 i
    have havsum : (∑ i, av i) < q := by
      exact a.2.2
    have hcard := syracuse_exact_prefix_finite_card_normalized q t av hav havsum
    have hsum :
        ∑ r ∈ E a, g r =
          ((E a).card : ℝ) * (2 / (2 : ℝ) ^ q) := by
      calc
        ∑ r ∈ E a, g r = ∑ r ∈ E a, (2 / (2 : ℝ) ^ q) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr' := (Finset.mem_filter.mp hr).2
          exact if_pos hr'.2.1
        _ = ((E a).card : ℝ) * (2 / (2 : ℝ) ^ q) := by
          simp [mul_comm]
    rw [hsum]
    have hcardE :
        ((E a).card : ℝ) /
            (2 ^ (q - 1) : ℝ) =
          1 / (2 : ℝ) ^ (∑ i, av i) := by
      simpa [E, av, syracuseShortPrefixEvent, Fintype.card_subtype] using hcard
    have hpow : (2 : ℝ) / (2 : ℝ) ^ q = 1 / (2 : ℝ) ^ (q - 1) := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      simp [pow_succ]
      field_simp
    rw [hpow]
    rw [← hcardE]
    field_simp
  have hcontract := finite_law_disjoint_l1 μ X E g hX hdisj
  have hresmass (r : Fin (2 ^ q)) :
      (μ (X ⁻¹' ({r} : Set (Fin (2 ^ q))))).toReal =
        (μ {ω | N ω % 2 ^ q = r.val}).toReal := by
    have hset : ∀ᵐ ω ∂μ,
        ω ∈ X ⁻¹' ({r} : Set (Fin (2 ^ q))) ↔
          ω ∈ ({ω : Ω | N ω % 2 ^ q = r.val} : Set Ω) := by
      exact ae_of_all μ (fun ω : Ω => by
        change syracuseShortPrefixResidue q (N ω) = r ↔
          (N ω % 2 ^ q = r.val)
        constructor
        · intro h
          exact congrArg Fin.val h
        · intro h
          exact Fin.ext h)
    exact congrArg ENNReal.toReal
      (measure_congr (hset.mono fun ω hω => propext hω))
  calc
    (∑ a : PositiveExponentPrefix t q,
        |(μ {ω | ∀ i : Fin t, syracuseExponent (N ω) i = (a.1 i).val}).toReal -
          1 / (2 : ℝ) ^ (∑ i, (a.1 i).val)|) =
        ∑ a : PositiveExponentPrefix t q,
          |(μ (X ⁻¹' (E a : Set (Fin (2 ^ q))))).toReal - ∑ r ∈ E a, g r| := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hmass a, hmodel a]
    _ ≤ ∑ r : Fin (2 ^ q),
        |(μ (X ⁻¹' ({r} : Set (Fin (2 ^ q))))).toReal - g r| := hcontract
    _ = ∑ r : Fin (2 ^ q),
        |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
          (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hresmass r]




set_option autoImplicit false

/-- A linear lower bound on the modulus exponent converts dyadic error to exponential decay. -/
theorem dyadic_error_le_exponential
    (K a : ℝ) (hK : 0 ≤ K) (q t : ℕ) (hqt : a * (t : ℝ) ≤ (q : ℝ)) :
    K / (2 : ℝ) ^ q ≤ K * Real.exp (-(a * Real.log 2) * (t : ℝ)) := by
  have hpow : (2 : ℝ) ^ q = Real.exp (Real.log 2 * (q : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Two exponential errors admit a common rate, independent of the size parameter. -/
theorem two_exponential_errors_le_common_rate
    (A K d e : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) (t : ℕ) :
    2 * (K * Real.exp (-e * (t : ℝ))) + 2 * (A * Real.exp (-d * (t : ℝ))) ≤
      (2 * (K + A)) * Real.exp (-min d e * (t : ℝ)) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have hd : Real.exp (-d * (t : ℝ)) ≤ Real.exp (-min d e * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left d e)) ht
  have he : Real.exp (-e * (t : ℝ)) ≤ Real.exp (-min d e * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right d e)) ht
  nlinarith [mul_le_mul_of_nonneg_left hd hA, mul_le_mul_of_nonneg_left he hK]



/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/


open MeasureTheory
open Set
open scoped BigOperators

set_option autoImplicit false

/-- The zero-coordinate Syracuse valuation law and the zero-coordinate geometric law agree. -/
theorem syracuse_empty_valuation_l1
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ) :
    (∑' a : Fin 0 → ℕ,
      |(μ {ω | syracuseValuationVector 0 N ω = a}).toReal -
        (positiveGeomTwoVector 0).real {a}|) = 0 := by
  have hsub : ∀ a b : Fin 0 → ℕ, a = b := by
    intro a b
    funext i
    exact Fin.elim0 i
  have hactual : ∀ a : Fin 0 → ℕ,
      (μ {ω | syracuseValuationVector 0 N ω = a}).toReal = 1 := by
    intro a
    rw [show {ω | syracuseValuationVector 0 N ω = a} = Set.univ by
      ext ω
      simp [hsub (syracuseValuationVector 0 N ω) a]]
    simp
  have hmodel : ∀ a : Fin 0 → ℕ,
      (positiveGeomTwoVector 0).real {a} = 1 := by
    intro a
    have hprob : (positiveGeomTwoVector 0).real Set.univ = 1 := by
      simp
    rw [show ({a} : Set (Fin 0 → ℕ)) = Set.univ by
      ext b
      simp [hsub b a]]
    exact hprob
  simp_rw [hactual, hmodel]
  simp



/-
  Countable joint-law comparison for a Syracuse valuation prefix.

  The finite good-prefix discrepancy is supplied by the disjoint short-prefix
  event contraction; the complement is the actual valuation tail.  The
  resulting estimate is the static one-tail decomposition needed before the
  logarithmic-density assembly.
-/


open MeasureTheory Set
open scoped BigOperators

set_option autoImplicit false

open scoped Classical in
theorem joint_l1_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N)
    (hAE : ∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω))
    (q t : ℕ) (hq : 0 < q) :
    (∑' a : Fin t → ℕ,
      |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
        (positiveGeomTwoVector t).real {a}|) ≤
      2 * (∑ r : Fin (2 ^ q),
        |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
          (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)|) +
        2 * (μ {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i}).toReal := by
  let X : Ω → (Fin t → ℕ) := syracuseValuationVector t N
  let p : (Fin t → ℕ) → ℝ := fun a =>
    (μ (X ⁻¹' ({a} : Set (Fin t → ℕ)))).toReal
  let g : (Fin t → ℕ) → ℝ := fun a =>
    (positiveGeomTwoVector t).real {a}
  have hX : Measurable X := measurable_syracuseValuationVector t N hN
  have hp : Summable p := by
    simpa [p] using countable_law_atoms_summable μ X hX
  have hg : Summable g := by
    simpa [g] using positiveGeomTwoVector_atoms_summable t
  have hp_total : (∑' a, p a) = 1 := by
    simpa [p] using countable_law_atoms_real_tsum μ X hX
  have hg_total : (∑' a, g a) = 1 := by
    simpa [g] using positiveGeomTwoVector_atoms_tsum t
  have hp_nonneg : ∀ a, 0 ≤ p a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hg_nonneg : ∀ a, 0 ≤ g a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hfinite :
      (∑ a ∈ shortPositiveVectorFinset t q, |p a - g a|) ≤
        ∑ r : Fin (2 ^ q),
          |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
            (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| := by
    rw [sum_over_shortPositiveVectorFinset]
    calc
      (∑ a : PositiveExponentPrefix t q,
          |p (positiveExponentPrefixValues a) -
            g (positiveExponentPrefixValues a)|) =
          ∑ a : PositiveExponentPrefix t q,
            |(μ {ω | ∀ i : Fin t,
                syracuseExponent (N ω) i = (a.1 i).val}).toReal -
              1 / (2 : ℝ) ^ (∑ i, (a.1 i).val)| := by
        apply Finset.sum_congr rfl
        intro a ha
        have hmass :
            (μ (X ⁻¹' ({positiveExponentPrefixValues a} :
              Set (Fin t → ℕ)))).toReal =
            (μ {ω | ∀ i : Fin t,
                syracuseExponent (N ω) i = (a.1 i).val}).toReal := by
          have hset :
              X ⁻¹' ({positiveExponentPrefixValues a} : Set (Fin t → ℕ)) =
                {ω | ∀ i : Fin t,
                  syracuseExponent (N ω) i = (a.1 i).val} := by
            ext ω
            change (syracuseValuationVector t N ω =
                positiveExponentPrefixValues a) ↔ _
            constructor
            · intro h i
              exact congrFun h i
            · intro h
              funext i
              exact h i
          exact congrArg ENNReal.toReal (congrArg μ hset)
        have hmodel :
            (positiveGeomTwoVector t).real
                {positiveExponentPrefixValues a} =
              1 / (2 : ℝ) ^ (∑ i, (a.1 i).val) := by
          exact positiveGeomTwoVector_atom_of_pos t
            (positiveExponentPrefixValues a) a.2.1
        simpa [p, g, X, hmass, hmodel]
      _ ≤ ∑ r : Fin (2 ^ q),
          |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
            (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| :=
        syracuse_short_prefix_l1 μ N hN hAE q t hq
  have htailF :
      (∑' a : {a // a ∉ shortPositiveVectorFinset t q}, p a) =
        (μ {ω | X ω ∉ shortPositiveVectorFinset t q}).toReal := by
    let E : Set (Fin t → ℕ) :=
      {a | a ∉ shortPositiveVectorFinset t q}
    let e : {a // a ∉ shortPositiveVectorFinset t q} ≃
        {a // a ∈ E} :=
      { toFun := fun a => ⟨a.1, by exact a.2⟩
        invFun := fun a => ⟨a.1, by exact a.2⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl }
    calc
      (∑' a : {a // a ∉ shortPositiveVectorFinset t q}, p a) =
          ∑' a : {a // a ∈ E}, p a := by
        simpa [E, e] using (e.tsum_eq (fun a => p a))
      _ = (μ (X ⁻¹' E)).toReal := by
        simpa [p] using countable_law_event_real_tsum μ X hX E
      _ = (μ {ω | X ω ∉ shortPositiveVectorFinset t q}).toReal := by
        congr 1
  have htail := measureReal_shortPositiveVectorFinset_compl_eq_valuation_tail
    μ t q N hAE
  have htail' :
      (∑' a : {a // a ∉ shortPositiveVectorFinset t q}, p a) =
        (μ {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i}).toReal := by
    rw [htailF]
    exact htail
  have hone := tsum_abs_sub_le_two_mul_finset_add_two_mul_compl
    p g (shortPositiveVectorFinset t q) hp hg hp_total hg_total hp_nonneg hg_nonneg
  calc
    (∑' a : Fin t → ℕ,
        |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
          (positiveGeomTwoVector t).real {a}|) =
        ∑' a : Fin t → ℕ, |p a - g a| := by
      rfl
    _ ≤ 2 * (∑ a ∈ shortPositiveVectorFinset t q, |p a - g a|) +
          2 * (∑' a : {a // a ∉ shortPositiveVectorFinset t q}, p a) := hone
    _ ≤ 2 * (∑ r : Fin (2 ^ q),
          |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
            (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)|) +
          2 * (∑' a : {a // a ∉ shortPositiveVectorFinset t q}, p a) := by
      gcongr
    _ = 2 * (∑ r : Fin (2 ^ q),
          |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
            (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)|) +
          2 * (μ {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i}).toReal := by
      rw [htail']



/-- Uniform exponential joint-law approximation to the positive geometric vector. -/
theorem joint_exponential_bound
    (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ),
        Measurable N → (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) →
        ∀ q t : ℕ, 0 < q → (2 + c) * (t : ℝ) ≤ (q : ℝ) →
          (∑ r : Fin (2 ^ q),
            |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
              (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤ K / (2 : ℝ) ^ q) →
          (∑' a : Fin t → ℕ,
            |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
              (positiveGeomTwoVector t).real {a}|) ≤
            C * Real.exp (-D * (t : ℝ)) := by
  obtain ⟨A, d, hA, hd, htail⟩ :=
    syracuse_valuation_tail_almost_uniform c K hc hK
  let e : ℝ := (2 + c) * Real.log 2
  have he : 0 < e := mul_pos (by linarith) (Real.log_pos (by norm_num))
  refine ⟨2 * (K + A), min d e, by positivity, lt_min hd he, ?_⟩
  intro Ω _ μ _ N hN hAE q t hq hqt hL1
  have ht := htail μ N hN hAE q t hq hqt hL1
  have ht_real :
      (μ {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i}).toReal ≤
        A * Real.exp (-d * (t : ℝ)) := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_ofReal (mul_nonneg hA.le (Real.exp_pos _).le)] at hr
    have hset :
        {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i} =
          {ω | q ≤ ∑ i ∈ Finset.range t,
            (3 * (syracuseStep^[i]) (N ω) + 1).factorization 2} := by
      ext ω
      simp only [syracuseExponent]
      change (q ≤ ∑ i : Fin t,
          (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2) ↔
        q ≤ ∑ i ∈ Finset.range t,
          (3 * (syracuseStep^[i]) (N ω) + 1).factorization 2
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ => (3 * (syracuseStep^[i]) (N ω) + 1).factorization 2) t]
    rw [hset]
    exact hr
  have hj := joint_l1_bound μ N hN hAE q t hq
  have herr := dyadic_error_le_exponential K (2 + c) hK q t hqt
  calc
    (∑' a : Fin t → ℕ,
        |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
          (positiveGeomTwoVector t).real {a}|) ≤
        2 * (∑ r : Fin (2 ^ q),
          |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
            (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)|) +
          2 * (μ {ω | q ≤ ∑ i : Fin t, syracuseExponent (N ω) i}).toReal := hj
    _ ≤ 2 * (K / (2 : ℝ) ^ q) + 2 * (A * Real.exp (-d * (t : ℝ))) := by
      gcongr
    _ ≤ 2 * (K * Real.exp (-e * (t : ℝ))) +
          2 * (A * Real.exp (-d * (t : ℝ))) := by
      gcongr
    _ ≤ (2 * (K + A)) * Real.exp (-min d e * (t : ℝ)) :=
      two_exponential_errors_le_common_rate A K d e hA.le hK t


end
end CollatzJointPackage

open CollatzJointPackage

theorem solution
    (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ A d : ℝ, 0 < A ∧ 0 < d ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ),
        Measurable N → (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) →
        ∀ q t : ℕ, (2 + c) * (t : ℝ) ≤ (q : ℝ) →
          (∑ r : Fin (2 ^ q),
            |(μ {ω | N ω % 2 ^ q = r.val}).toReal -
              (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤ K / (2 : ℝ) ^ q) →
          (∑' a : Fin t → ℕ,
            |(μ {ω | ∀ i : Fin t,
                (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal -
              (if ∀ i : Fin t, 0 < a i then 1 / (2 : ℝ) ^ (∑ i, a i) else 0)|) ≤
            A * Real.exp (-d * (t : ℝ)) := by
  obtain ⟨A, d, hA, hd, h⟩ := CollatzJointPackage.joint_exponential_bound c K hc hK
  refine ⟨A, d, hA, hd, ?_⟩
  intro Ω _ μ _ N hN hAE q t hqt hL1
  have hb :
      (∑' a : Fin t → ℕ,
        |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
          (positiveGeomTwoVector t).real {a}|) ≤ A * Real.exp (-d * (t : ℝ)) := by
    by_cases hq : 0 < q
    · exact h μ N hN hAE q t hq hqt hL1
    · have hq0 : q = 0 := by omega
      have htR : (t : ℝ) = 0 := by
        rw [hq0] at hqt
        norm_num at hqt
        have ht_nonneg : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        nlinarith [mul_nonneg hc.le ht_nonneg]
      have ht0 : t = 0 := by exact_mod_cast htR
      subst t
      rw [syracuse_empty_valuation_l1]
      positivity
  have heq :
      (∑' a : Fin t → ℕ,
        |(μ {ω | ∀ i : Fin t,
            (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i}).toReal -
          (if ∀ i : Fin t, 0 < a i then 1 / (2 : ℝ) ^ (∑ i, a i) else 0)|) =
        ∑' a : Fin t → ℕ,
          |(μ {ω | syracuseValuationVector t N ω = a}).toReal -
            (positiveGeomTwoVector t).real {a}| := by
    apply tsum_congr
    intro a
    have hmodel : (positiveGeomTwoVector t).real {a} =
        if ∀ i : Fin t, 0 < a i then 1 / (2 : ℝ) ^ (∑ i, a i) else 0 := by
      by_cases ha : ∀ i : Fin t, 0 < a i
      · rw [if_pos ha]
        exact positiveGeomTwoVector_atom_of_pos t a ha
      · simp [positiveGeomTwoVector_real_singleton, ha]
    rw [← hmodel]
    have hs :
        {ω | ∀ i : Fin t,
          (3 * (syracuseStep^[i.val]) (N ω) + 1).factorization 2 = a i} =
          {ω | syracuseValuationVector t N ω = a} := by
      ext ω
      constructor
      · intro hcoords
        funext i
        exact hcoords i
      · intro hcoords i
        exact congrFun hcoords i
    rw [hs]
  rw [heq]
  exact hb
