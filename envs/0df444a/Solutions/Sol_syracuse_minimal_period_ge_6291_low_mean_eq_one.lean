-- Prove2me | solution 1 for syracuse_minimal_period_ge_6291_low_mean_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-02T00:49:23.244738+00:00
-- url     : https://prove2.me/submissions/50d0932b-ac1c-4a8c-9c0e-d45bf6bb50c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
import Theorems.Thm_syracuse_valuation_word_rotation_rigidity
import Theorems.Thm_syracuse_primitive_low_mean_word_affine_nondivisibility

set_option autoImplicit false

/-
SOURCE-ONLY CONDITIONAL REDUCTION / PROOF SKETCH, NOT A COMPLETED PROOF.
The last import is a prospective, unpublished Open word-arithmetic child,
tracked by primitive_word_child_problem_v01.json. Its nondivisibility assertion
is unresolved. No public UUID, proof, or acceptance for that child is assumed
as an accomplished fact. This file cannot establish the low-mean tail until
that child is proved and its actual exported type/dependencies are checked.
No local compilation, kernel verification, publication, or remote verification
has been performed for this packet.

The three reviewed mathematical namespace bodies below are preserved unchanged
from cycle_syracuse_affine_endpoint_draft_01.lean,
cycle_syracuse_word_primitivity_bridge_draft_01.lean, and
cycle_syracuse_valuation_one_density_draft_01.lean. They are flattened here;
there are no local draft or private Solutions imports. The last body supplies
actual-orbit exponent positivity, not a new public low-mean assumption.

The final solution has exactly the low-mean tail type recorded in
mean_tail_child_problem_v01.json, now published as target
47d69530-0846-4d09-a212-6a25ea00aa9e (published_mean_tail_child.json).
This records target identity only, not frontier or proof-sketch acceptance.
It constructs the ACTUAL indexed valuation
word and transports length, sum, positivity, and least-return primitivity.
Only for this actual orbit does it use the public cycle power gap and endpoint
divisibility. The Open child separately receives an EXPLICIT power-gap premise
for its arbitrary word. No candidate realization or converse is implemented.
No optional all-rotation baseline filter, Mean import, upper state/period cap,
word-symmetry assumption, or completed parent/tail/Collatz claim is added.

Public same-pin definitions/supports: syracuseStep;
syracuseOffsetMod (exports the canonical syracuseAffineConstant),
864533ea-15c3-4810-a04c-d66a460333b7;
syracuse_cycle_pow_two_gt_pow_three, 955877f3-88bd-4837-b1d9-2e4467430637;
syracuse_valuation_word_rotation_rigidity, 9d080639-84a9-4f79-a536-21f43d096863.
Existing community affine/power-gap work and accepted small-cycle image-oddness
helper text are credited in low_mean_word_reduction_explanation_v01.md.
Mathlib pin: 0df444a360eaa60ab8c11dca51a86af692955474; Lean v4.33.1.
The added sum transport uses List.sum_ofFn and Finset.sum_range, generated in
Mathlib/Algebra/BigOperators/Fin.lean, with List.length_ofFn and List.mem_ofFn.
-/

open scoped BigOperators

namespace CollatzSyracuseAffineEndpointDraft01

private theorem step_factorization (n : ℕ) :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/-- Fin-indexed auxiliary form. Head induction uses the canonical cons
recurrence and starts the tail orbit at syracuseStep m. -/
private theorem affine_endpoint_fin (m p : ℕ) :
    2 ^ (∑ i : Fin p, (3 * syracuseStep^[i.val] m + 1).factorization 2) *
        syracuseStep^[p] m =
      3 ^ p * m + syracuseAffineConstant
        (List.ofFn (fun i : Fin p =>
          (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
  induction p generalizing m with
  | zero =>
      simp [syracuseAffineConstant]
  | succ p ih =>
      let a : ℕ := (3 * m + 1).factorization 2
      let n : ℕ := syracuseStep m
      let e : Fin p → ℕ := fun i =>
        (3 * syracuseStep^[i.val] n + 1).factorization 2
      have hsum :
          (∑ i : Fin (p + 1), (3 * syracuseStep^[i.val] m + 1).factorization 2) =
            a + (∑ i : Fin p, e i) := by
        simpa only [Fin.val_zero, Fin.val_succ, Function.iterate_zero_apply,
          Function.iterate_succ_apply, a, n, e] using
          (Fin.sum_univ_succ (fun i : Fin (p + 1) =>
            (3 * syracuseStep^[i.val] m + 1).factorization 2))
      have hword :
          List.ofFn (fun i : Fin (p + 1) =>
            (3 * syracuseStep^[i.val] m + 1).factorization 2) =
            a :: List.ofFn e := by
        simpa only [Fin.val_zero, Fin.val_succ, Function.iterate_zero_apply,
          Function.iterate_succ_apply, a, n, e] using
          (List.ofFn_succ (f := fun i : Fin (p + 1) =>
            (3 * syracuseStep^[i.val] m + 1).factorization 2))
      have hconstant :
          syracuseAffineConstant (List.ofFn (fun i : Fin (p + 1) =>
            (3 * syracuseStep^[i.val] m + 1).factorization 2)) =
            3 ^ p + 2 ^ a * syracuseAffineConstant (List.ofFn e) := by
        rw [hword]
        simp only [syracuseAffineConstant, List.length_ofFn]
      have htail :
          2 ^ (∑ i : Fin p, e i) * syracuseStep^[p] n =
            3 ^ p * n + syracuseAffineConstant (List.ofFn e) := by
        simpa only [n, e] using ih (syracuseStep m)
      have hstep : 2 ^ a * n = 3 * m + 1 := by
        change 2 ^ ((3 * m + 1).factorization 2) * syracuseStep m = 3 * m + 1
        exact step_factorization m
      calc
        2 ^ (∑ i : Fin (p + 1),
            (3 * syracuseStep^[i.val] m + 1).factorization 2) *
            syracuseStep^[p + 1] m =
            2 ^ a * (2 ^ (∑ i : Fin p, e i) * syracuseStep^[p] n) := by
          rw [hsum, Nat.pow_add, Function.iterate_succ_apply, Nat.mul_assoc]
        _ = 2 ^ a * (3 ^ p * n + syracuseAffineConstant (List.ofFn e)) := by
          rw [htail]
        _ = 3 ^ p * (2 ^ a * n) + 2 ^ a * syracuseAffineConstant (List.ofFn e) := by
          ring
        _ = 3 ^ p * (3 * m + 1) + 2 ^ a * syracuseAffineConstant (List.ofFn e) := by
          rw [hstep]
        _ = 3 ^ (p + 1) * m +
            (3 ^ p + 2 ^ a * syracuseAffineConstant (List.ofFn e)) := by
          rw [Nat.pow_succ]
          ring
        _ = 3 ^ (p + 1) * m + syracuseAffineConstant
            (List.ofFn (fun i : Fin (p + 1) =>
              (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
          rw [hconstant]

/-- Exact endpoint for the actual accelerated orbit, with its actual removed
exponents. No positivity, oddness, or return hypothesis is required. -/
theorem syracuse_affine_endpoint (m p : ℕ) :
    2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
        syracuseStep^[p] m =
      3 ^ p * m + syracuseAffineConstant
        (List.ofFn (fun i : Fin p =>
          (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
  rw [Finset.sum_range (fun i : ℕ =>
    (3 * syracuseStep^[i] m + 1).factorization 2)]
  exact affine_endpoint_fin m p

/-- The natural-number cycle identity D*m=C. Truncated subtraction causes no
hidden gap: Nat.sub_mul and cancellation prove this even for p=0. -/
theorem syracuse_cycle_affine_constant_mul (m p : ℕ)
    (hcycle : syracuseStep^[p] m = m) :
    (2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) -
        3 ^ p) * m =
      syracuseAffineConstant (List.ofFn (fun i : Fin p =>
        (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
  have hendpoint := syracuse_affine_endpoint m p
  rw [hcycle] at hendpoint
  rw [Nat.sub_mul, hendpoint, Nat.add_sub_cancel_left]

/-- Actual cycles necessarily satisfy divisibility of the canonical numerator
by D. The witness is the actual starting value m, not a candidate word root. -/
theorem syracuse_cycle_affine_constant_dvd (m p : ℕ)
    (hcycle : syracuseStep^[p] m = m) :
    (2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) -
        3 ^ p) ∣
      syracuseAffineConstant (List.ofFn (fun i : Fin p =>
        (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
  exact ⟨m, (syracuse_cycle_affine_constant_mul m p hcycle).symm⟩

/-- For a positive starting value and a positive return time, the public strict
power gap ensures that the cycle denominator D is strictly positive. -/
theorem syracuse_cycle_affine_denominator_pos (m p : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hcycle : syracuseStep^[p] m = m) :
    0 < 2 ^ (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) - 3 ^ p := by
  exact Nat.sub_pos_iff_lt.mpr
    (syracuse_cycle_pow_two_gt_pow_three m p hm hp hcycle)

end CollatzSyracuseAffineEndpointDraft01

namespace CollatzSyracuseWordPrimitivityBridgeDraft01

/-- For an actual positive Syracuse return orbit, least positive return is
exactly primitivity of its indexed valuation word under proper rotations. -/
theorem least_positive_return_iff_actual_word_rotation_primitive
    (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m) :
    (∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) ↔
      (∀ d : ℕ, 0 < d → d < p →
        (List.ofFn (fun i : Fin p =>
          (3 * syracuseStep^[i.val] m + 1).factorization 2)).rotate d ≠
        List.ofFn (fun i : Fin p =>
          (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
  let e : ℕ → ℕ := fun i => (3 * syracuseStep^[i] m + 1).factorization 2
  let w : List ℕ := List.ofFn (fun i : Fin p => e i.val)
  change (∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) ↔
    (∀ d : ℕ, 0 < d → d < p → w.rotate d ≠ w)
  have hwlen : w.length = p := by
    simp only [w, List.length_ofFn]
  have hperiodic : Function.IsPeriodicPt syracuseStep p m := hcyc
  have hmod (j : ℕ) : e (j % p) = e j := by
    change (3 * syracuseStep^[j % p] m + 1).factorization 2 =
      (3 * syracuseStep^[j] m + 1).factorization 2
    rw [hperiodic.iterate_mod_apply j]
  have hget (i : ℕ) (hi : i < p) :
      w[i]'(by simpa only [hwlen] using hi) = e i := by
    simp only [w, List.getElem_ofFn]
  have hgetrot (d i : ℕ) (hi : i < p) :
      (w.rotate d)[i]'(by simpa only [List.length_rotate, hwlen] using hi) =
        e ((i + d) % p) := by
    rw [List.getElem_rotate]
    simpa only [hwlen] using hget ((i + d) % p) (Nat.mod_lt _ hp)
  have hrot_iff (d : ℕ) : w.rotate d = w ↔ syracuseStep^[d] m = m := by
    constructor
    · intro hrot
      apply syracuse_valuation_word_rotation_rigidity m p d hm hp hcyc
      intro i hi
      change e (i + d) = e i
      calc
        e (i + d) = e ((i + d) % p) := (hmod (i + d)).symm
        _ = (w.rotate d)[i]'(by
          simpa only [List.length_rotate, hwlen] using hi) := (hgetrot d i hi).symm
        _ = w[i]'(by simpa only [hwlen] using hi) := by
          simp only [hrot]
        _ = e i := hget i hi
    · intro hret
      refine List.ext_getElem (List.length_rotate w d) ?_
      intro i hiRot hiW
      have hi : i < p := by simpa only [hwlen] using hiW
      calc
        (w.rotate d)[i]'hiRot = e ((i + d) % p) := hgetrot d i hi
        _ = e (i + d) := hmod (i + d)
        _ = e i := by
          change (3 * syracuseStep^[i + d] m + 1).factorization 2 =
            (3 * syracuseStep^[i] m + 1).factorization 2
          rw [Function.iterate_add_apply, hret]
        _ = w[i]'hiW := (hget i hi).symm
  constructor
  · intro hmin d hd hdp hrot
    exact hmin d hd hdp ((hrot_iff d).mp hrot)
  · intro hprimitive k hk hkp hret
    exact hprimitive k hk hkp ((hrot_iff k).mpr hret)

end CollatzSyracuseWordPrimitivityBridgeDraft01

namespace CollatzSyracuseValuationOneDensityDraft01

/-- Positive exponents other than one are at least two. Summing this elementary
pointwise fact retains the multiplicity of every indexed position. -/
theorem finite_count_ones_lower_bound (p : ℕ) (e : ℕ → ℕ)
    (he : ∀ i : ℕ, i < p → 1 ≤ e i) :
    2 * p ≤ (∑ i ∈ Finset.range p, e i) +
      ((Finset.range p).filter (fun i => e i = 1)).card := by
  have hterm : ∀ i ∈ Finset.range p,
      2 ≤ e i + (if e i = 1 then 1 else 0) := by
    intro i hi
    have hei : 1 ≤ e i := he i (Finset.mem_range.mp hi)
    by_cases hone : e i = 1
    · simp [hone]
    · simp only [if_neg hone, Nat.add_zero]
      omega
  calc
    2 * p = (∑ _i ∈ Finset.range p, (2 : ℕ)) := by
      simp [Nat.nsmul_eq_mul, Nat.mul_comm]
    _ ≤ (∑ i ∈ Finset.range p, (e i + (if e i = 1 then 1 else 0))) :=
      Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range p, e i) +
        ((Finset.range p).filter (fun i => e i = 1)).card := by
      rw [Finset.sum_add_distrib, ← Finset.card_filter]

/-- Conditional strict density bound for an arbitrary positive exponent word.
The strict low-mean hypothesis is supplied, not established by this theorem. -/
theorem finite_count_ones_of_low_mean (p : ℕ) (e : ℕ → ℕ)
    (he : ∀ i : ℕ, i < p → 1 ≤ e i)
    (hlow : 200 * (∑ i ∈ Finset.range p, e i) < 317 * p) :
    83 * p < 200 * ((Finset.range p).filter (fun i => e i = 1)).card := by
  have hcount := finite_count_ones_lower_bound p e he
  have hscaled := Nat.mul_le_mul_left 200 hcount
  omega

/-- Every accelerated image is odd; no oddness hypothesis on the input is
needed. In particular this is not a claim about the classical Collatz map. -/
theorem step_odd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

/-- A point returning after a positive number of steps is itself an image. -/
theorem periodic_point_odd (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) : Odd m := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  rw [← hcycle, Function.iterate_succ_apply']
  exact step_odd _

/-- Every forward state of a positive-return orbit is odd, including state zero.
There is no initial positivity or oddness hypothesis and no least-period claim. -/
theorem periodic_state_odd (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (i : ℕ) :
    Odd (syracuseStep^[i] m) := by
  cases i with
  | zero =>
      simpa only [Function.iterate_zero_apply] using periodic_point_odd m p hp hcycle
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact step_odd _

/-- Odd inputs give a nonzero even value of 3*n+1, so its two-adic valuation
is positive. The primality and nonzero hypotheses are supplied explicitly. -/
theorem valuation_ge_one_of_odd (n : ℕ) (hn : Odd n) :
    1 ≤ (3 * n + 1).factorization 2 := by
  have hnmod : n % 2 = 1 := Nat.odd_iff.mp hn
  have heven : (3 * n + 1) % 2 = 0 := by omega
  have hdvd : 2 ∣ 3 * n + 1 := Nat.dvd_iff_mod_eq_zero.mpr heven
  have hpositive : 0 < (3 * n + 1).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two
      (by omega : 3 * n + 1 ≠ 0) hdvd
  exact Nat.succ_le_of_lt hpositive

/-- The actual removed exponent is at least one at every state of a
positive-return Syracuse orbit, without assuming an odd starting input. -/
theorem periodic_valuation_ge_one (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (i : ℕ) :
    1 ≤ (3 * syracuseStep^[i] m + 1).factorization 2 := by
  exact valuation_ge_one_of_odd (syracuseStep^[i] m)
    (periodic_state_odd m p hp hcycle i)

/-- The counting inequality instantiated with the actual cycle valuations. -/
theorem syracuse_cycle_count_ones_lower_bound (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) :
    2 * p ≤ (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) +
      ((Finset.range p).filter (fun i =>
        (3 * syracuseStep^[i] m + 1).factorization 2 = 1)).card := by
  exact finite_count_ones_lower_bound p
    (fun i => (3 * syracuseStep^[i] m + 1).factorization 2)
    (fun i _ => periodic_valuation_ge_one m p hp hcycle i)

/-- CONDITIONAL: more than 83/200 = 41.5 percent of the p indexed cycle
positions have valuation one, assuming the explicit strict low-mean bound.
This structural restriction does not exclude such cycles or prove the tail. -/
theorem syracuse_cycle_count_ones_of_low_mean (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m)
    (hlow : 200 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) < 317 * p) :
    83 * p < 200 * ((Finset.range p).filter (fun i =>
      (3 * syracuseStep^[i] m + 1).factorization 2 = 1)).card := by
  exact finite_count_ones_of_low_mean p
    (fun i => (3 * syracuseStep^[i] m + 1).factorization 2)
    (fun i _ => periodic_valuation_ge_one m p hp hcycle i) hlow

end CollatzSyracuseValuationOneDensityDraft01

/-- PROOF SKETCH ONLY: the exact low-mean tail follows if the separately tracked
Open pure-word nondivisibility child is established. -/
theorem solution (m p : ℕ) (hm : 0 < m)
    (hp : 6291 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m)
    (hlow : 200 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) < 317 * p) :
    m = 1 := by
  have hp0 : 0 < p := by omega
  let w : List ℕ := List.ofFn (fun i : Fin p =>
    (3 * syracuseStep^[i.val] m + 1).factorization 2)
  have hwlen : w.length = p := by
    simp only [w, List.length_ofFn]
  have hwsum : w.sum = ∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2 := by
    change (List.ofFn (fun i : Fin p =>
      (3 * syracuseStep^[i.val] m + 1).factorization 2)).sum = _
    rw [List.sum_ofFn, Finset.sum_range (fun i : ℕ =>
      (3 * syracuseStep^[i] m + 1).factorization 2)]
  have hpositive : ∀ a ∈ w, 0 < a := by
    intro a ha
    change a ∈ List.ofFn (fun i : Fin p =>
      (3 * syracuseStep^[i.val] m + 1).factorization 2) at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (CollatzSyracuseValuationOneDensityDraft01.periodic_valuation_ge_one
        m p hp0 hcyc i.val)
  have hlength : 6291 ≤ w.length := by
    simpa only [hwlen] using hp
  have hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w := by
    rw [hwlen]
    exact
      (CollatzSyracuseWordPrimitivityBridgeDraft01.least_positive_return_iff_actual_word_rotation_primitive
        m p hm hp0 hcyc).mp hmin
  have hdenominator : 0 < 2 ^ w.sum - 3 ^ w.length := by
    rw [hwsum, hwlen]
    exact CollatzSyracuseAffineEndpointDraft01.syracuse_cycle_affine_denominator_pos
      m p hm hp0 hcyc
  have hgap : 3 ^ w.length < 2 ^ w.sum := Nat.sub_pos_iff_lt.mp hdenominator
  have hlowWord : 200 * w.sum < 317 * w.length := by
    simpa only [hwsum, hwlen] using hlow
  have hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
    rw [hwsum, hwlen]
    exact CollatzSyracuseAffineEndpointDraft01.syracuse_cycle_affine_constant_dvd
      m p hcyc
  have hnot : ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w :=
    syracuse_primitive_low_mean_word_affine_nondivisibility
      w hpositive hlength hprimitive hgap hlowWord
  exact False.elim (hnot hdiv)
