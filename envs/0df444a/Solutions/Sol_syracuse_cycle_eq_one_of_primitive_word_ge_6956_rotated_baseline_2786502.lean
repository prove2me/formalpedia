-- Prove2me | solution 1 for syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:56.693567+00:00
-- url     : https://prove2.me/submissions/e9989ff7-0ee5-416e-a2f0-150efe225bce

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_period_le_6290_eq_one
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
import Theorems.Thm_syracuse_valuation_word_rotation_rigidity
import Theorems.Thm_syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306
import Theorems.Thm_syracuse_cycle_eq_one_of_state_baseline_budget_violation
import Theorems.Thm_syracuse_no_cycle_below_2310000
import Theorems.Thm_syracuse_power_gap_baseline_budget_period_sparse_6291
import Theorems.Thm_syracuse_word_length_6291_affine_nondivisibility
import Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502

/-
  Attribution.
  Helper lemmas copied verbatim from accepted Prove2me submission
  50d0932b-ac1c-4a8c-9c0e-d45bf6bb50c1 by user 090844a7-327d-477a-b08e-2937c520007f (FakeMink) (Apache-2.0 via Prove2me terms):
    namespace CollatzSyracuseAffineEndpointDraft01: step_factorization,
      affine_endpoint_fin, syracuse_affine_endpoint, syracuse_cycle_affine_constant_mul,
      syracuse_cycle_affine_constant_dvd, syracuse_cycle_affine_denominator_pos;
    namespace CollatzSyracuseWordPrimitivityBridgeDraft01:
      least_positive_return_iff_actual_word_rotation_primitive;
    namespace CollatzSyracuseValuationOneDensityDraft01: step_odd, periodic_point_odd,
      periodic_state_odd, valuation_ge_one_of_odd, periodic_valuation_ge_one.
  Changes: every copied declaration made `private`; original namespaces kept as noted;
  bodies unchanged.
  Adapted (not verbatim) in `solution`: the construction of the cycle valuation word
  (hwlen/hwsum/hpositive/hprimitive/hdiv/hgap) follows the `solution` of 50d0932b; the
  budget-violation case split follows accepted submission
  8c51a6dd-5d96-423e-b2f3-2b4e0e715779 by the same user (Apache-2.0 via Prove2me terms),
  and the `by_cases` / push-negation split on the rotated baseline follows accepted
  submission 26ec230a-e6f3-4394-ab2b-3cc335cd34ad by the same user (same terms).
  New: least-period reduction via Function.minimalPeriod, the use of
  syracuse_period_le_6290_eq_one, the rotated-baseline / sparse-period case analysis, and
  the final application of the leaf hypothesis.
-/

set_option autoImplicit false

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
private theorem syracuse_affine_endpoint (m p : ℕ) :
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
private theorem syracuse_cycle_affine_constant_mul (m p : ℕ)
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
private theorem syracuse_cycle_affine_constant_dvd (m p : ℕ)
    (hcycle : syracuseStep^[p] m = m) :
    (2 ^ (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) -
        3 ^ p) ∣
      syracuseAffineConstant (List.ofFn (fun i : Fin p =>
        (3 * syracuseStep^[i.val] m + 1).factorization 2)) := by
  exact ⟨m, (syracuse_cycle_affine_constant_mul m p hcycle).symm⟩

/-- For a positive starting value and a positive return time, the public strict
power gap ensures that the cycle denominator D is strictly positive. -/
private theorem syracuse_cycle_affine_denominator_pos (m p : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hcycle : syracuseStep^[p] m = m) :
    0 < 2 ^ (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) - 3 ^ p := by
  exact Nat.sub_pos_iff_lt.mpr
    (syracuse_cycle_pow_two_gt_pow_three m p hm hp hcycle)

end CollatzSyracuseAffineEndpointDraft01

namespace CollatzSyracuseWordPrimitivityBridgeDraft01

/-- For an actual positive Syracuse return orbit, least positive return is
exactly primitivity of its indexed valuation word under proper rotations. -/
private theorem least_positive_return_iff_actual_word_rotation_primitive
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

/-- Every accelerated image is odd; no oddness hypothesis on the input is
needed. In particular this is not a claim about the classical Collatz map. -/
private theorem step_odd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

/-- A point returning after a positive number of steps is itself an image. -/
private theorem periodic_point_odd (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) : Odd m := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  rw [← hcycle, Function.iterate_succ_apply']
  exact step_odd _

/-- Every forward state of a positive-return orbit is odd, including state zero.
There is no initial positivity or oddness hypothesis and no least-period claim. -/
private theorem periodic_state_odd (m p : ℕ) (hp : 0 < p)
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
private theorem valuation_ge_one_of_odd (n : ℕ) (hn : Odd n) :
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
private theorem periodic_valuation_ge_one (m p : ℕ) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (i : ℕ) :
    1 ≤ (3 * syracuseStep^[i] m + 1).factorization 2 := by
  exact valuation_ge_one_of_odd (syracuseStep^[i] m)
    (periodic_state_odd m p hp hcycle i)

end CollatzSyracuseValuationOneDensityDraft01

theorem solution
    (hleaf : ∀ w : List ℕ,
      (∀ a ∈ w, 0 < a) →
      6956 ≤ w.length →
      (∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w) →
      3 ^ w.length < 2 ^ w.sum →
      200 * w.sum < 317 * w.length →
      306 * w.sum < 485 * w.length →
      (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤ (3 * 2310000 + 1 : ℕ) ^ w.length →
      (∀ d : ℕ, d < w.length →
        (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)) →
      ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w)
    (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hcyc : syracuseStep^[p] m = m) :
    m = 1 := by
  classical
  -- pass to the least period `q` of `m`
  have hmem : m ∈ Function.periodicPts syracuseStep :=
    Function.mk_mem_periodicPts hp hcyc
  have hq0 : 0 < Function.minimalPeriod syracuseStep m :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hqcyc : syracuseStep^[Function.minimalPeriod syracuseStep m] m = m :=
    Function.isPeriodicPt_minimalPeriod syracuseStep m
  have hmin : ∀ k : ℕ, 0 < k → k < Function.minimalPeriod syracuseStep m →
      syracuseStep^[k] m ≠ m := fun k hk hkq =>
    Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (Nat.pos_iff_ne_zero.mp hk) hkq
  generalize Function.minimalPeriod syracuseStep m = q at hq0 hqcyc hmin
  -- short least periods are already excluded on the platform
  by_cases hsmall : q ≤ 6290
  · exact syracuse_period_le_6290_eq_one m q hm hq0 hsmall hqcyc
  have hq6291 : 6291 ≤ q := by omega
  -- high mean valuation forces the trivial cycle
  by_cases hhigh : 485 * q ≤ 306 * (∑ i ∈ Finset.range q,
      (3 * syracuseStep^[i] m + 1).factorization 2)
  · exact syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306 m q hm hq0 hqcyc hhigh
  -- a violated 2310000 state-baseline budget forces the trivial cycle
  by_cases hbud : (2 : ℕ) ^ (∑ i ∈ Finset.range q,
      (3 * syracuseStep^[i] m + 1).factorization 2) * (2310000 : ℕ) ^ q ≤
      (3 * 2310000 + 1 : ℕ) ^ q
  swap
  · apply syracuse_cycle_eq_one_of_state_baseline_budget_violation 2310000 m q hm hq0 hqcyc
    · intro y hy hret hyB
      exact syracuse_no_cycle_below_2310000 y q hy hq0 (by omega) hret
    · exact Nat.lt_of_not_le hbud
  exfalso
  -- the actual valuation word of the least-period cycle
  let w : List ℕ := List.ofFn (fun i : Fin q =>
    (3 * syracuseStep^[i.val] m + 1).factorization 2)
  have hwlen : w.length = q := by
    simp only [w, List.length_ofFn]
  have hwsum : w.sum = ∑ i ∈ Finset.range q,
      (3 * syracuseStep^[i] m + 1).factorization 2 := by
    change (List.ofFn (fun i : Fin q =>
      (3 * syracuseStep^[i.val] m + 1).factorization 2)).sum = _
    rw [List.sum_ofFn, Finset.sum_range (fun i : ℕ =>
      (3 * syracuseStep^[i] m + 1).factorization 2)]
  have hpositive : ∀ a ∈ w, 0 < a := by
    intro a ha
    change a ∈ List.ofFn (fun i : Fin q =>
      (3 * syracuseStep^[i.val] m + 1).factorization 2) at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (CollatzSyracuseValuationOneDensityDraft01.periodic_valuation_ge_one
        m q hq0 hqcyc i.val)
  have hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w := by
    rw [hwlen]
    exact
      (CollatzSyracuseWordPrimitivityBridgeDraft01.least_positive_return_iff_actual_word_rotation_primitive
        m q hm hq0 hqcyc).mp hmin
  have hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
    rw [hwsum, hwlen]
    exact CollatzSyracuseAffineEndpointDraft01.syracuse_cycle_affine_constant_dvd m q hqcyc
  have hgap : 3 ^ w.length < 2 ^ w.sum := by
    rw [hwsum, hwlen]
    exact syracuse_cycle_pow_two_gt_pow_three m q hm hq0 hqcyc
  have hlowSharp : 306 * w.sum < 485 * w.length := by
    rw [hwsum, hwlen]
    omega
  have hlow : 200 * w.sum < 317 * w.length := by
    omega
  have hbudW : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length := by
    rw [hwsum, hwlen]
    exact hbud
  -- some rotation below the 2786502 baseline: excluded on the platform
  by_cases hrot : ∀ d : ℕ, d < w.length →
      (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)
  swap
  · push Not at hrot
    exact syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502
      w hpositive hgap hlowSharp hrot hdiv
  -- sparse periods: `q = 6291` (excluded) or `6956 ≤ q` (the leaf)
  have hsparse : w.length = 6291 ∨ 6956 ≤ w.length :=
    syracuse_power_gap_baseline_budget_period_sparse_6291 w.length w.sum
      (by omega) hgap hbudW
  rcases hsparse with h6291 | h6956
  · exact syracuse_word_length_6291_affine_nondivisibility w hpositive h6291 hgap hlowSharp hdiv
  · exact hleaf w hpositive h6956 hprimitive hgap hlow hlowSharp hbudW hrot hdiv
