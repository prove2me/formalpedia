-- Prove2me | solution 1 for syracuse_primitive_word_affine_nondivisibility_mean_lt_485_over_306
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-02T04:02:40.77557+00:00
-- url     : https://prove2.me/submissions/8c51a6dd-5d96-423e-b2f3-2b4e0e715779
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_cycle_eq_one_of_state_baseline_budget_violation
import Theorems.Thm_syracuse_no_cycle_below_2310000
import Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_with_baseline_budget

set_option autoImplicit false

-- The complete corrected realization construction is copied from accepted9675.
namespace CollatzAffineWordRotationDraft01

private theorem three_pow_odd (k : ℕ) : Odd ((3 : ℕ) ^ k) := by
  have hthree : Odd (3 : ℕ) := ⟨1, by norm_num⟩
  exact Odd.pow hthree

private theorem two_pow_even (k : ℕ) (hk : 0 < k) : Even ((2 : ℕ) ^ k) := by
  have htwo : Even (2 : ℕ) := ⟨1, by norm_num⟩
  exact Even.pow_of_ne_zero htwo (Nat.ne_of_gt hk)

/-- Canonical affine constants compose by concatenating their exponent words. -/
theorem affine_constant_append (u v : List ℕ) :
    syracuseAffineConstant (u ++ v) =
      3 ^ v.length * syracuseAffineConstant u +
        2 ^ u.sum * syracuseAffineConstant v := by
  induction u with
  | nil =>
      simp [syracuseAffineConstant]
  | cons a u ih =>
      simp only [List.cons_append, syracuseAffineConstant, List.length_append,
        List.sum_cons, ih, Nat.pow_add]
      ring

/-- Appending one exponent adds the final dyadic prefix term. -/
theorem affine_constant_append_singleton (as : List ℕ) (a : ℕ) :
    syracuseAffineConstant (as ++ [a]) =
      3 * syracuseAffineConstant as + 2 ^ as.sum := by
  rw [affine_constant_append]
  simp [syracuseAffineConstant]

/-- Subtraction-free one-position rotation identity, valid for all words. -/
theorem affine_constant_rotation_balance (a : ℕ) (as : List ℕ) :
    2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
      3 * syracuseAffineConstant (a :: as) + 2 ^ (a + as.sum) := by
  rw [affine_constant_append_singleton]
  simp only [syracuseAffineConstant, Nat.pow_add, Nat.pow_succ]
  ring

/-- Under an explicit arithmetic gap, the balanced identity becomes
2^a*C(rotated word)=3*C(original word)+D, with natural D. -/
theorem affine_constant_rotation (a : ℕ) (as : List ℕ)
    (hgap : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum)) :
    2 ^ a * syracuseAffineConstant (as ++ [a]) =
      3 * syracuseAffineConstant (a :: as) +
        (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
  have hcancel :
      2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
        (3 * syracuseAffineConstant (a :: as) +
          (2 ^ (a + as.sum) - 3 ^ (as.length + 1))) + 3 ^ (as.length + 1) := by
    calc
      2 ^ a * syracuseAffineConstant (as ++ [a]) + 3 ^ (as.length + 1) =
          3 * syracuseAffineConstant (a :: as) + 2 ^ (a + as.sum) :=
        affine_constant_rotation_balance a as
      _ = 3 * syracuseAffineConstant (a :: as) +
          ((2 ^ (a + as.sum) - 3 ^ (as.length + 1)) + 3 ^ (as.length + 1)) := by
        rw [Nat.sub_add_cancel hgap]
      _ = (3 * syracuseAffineConstant (a :: as) +
          (2 ^ (a + as.sum) - 3 ^ (as.length + 1))) + 3 ^ (as.length + 1) :=
        (Nat.add_assoc _ _ _).symm
  exact Nat.add_right_cancel hcancel

/-- A candidate denominator's positivity gives a purely arithmetic power gap.
This is not an actual-cycle theorem and assumes no candidate realization. -/
theorem power_gap_of_denominator_pos (w : List ℕ)
    (hD : 0 < 2 ^ w.sum - 3 ^ w.length) :
    3 ^ w.length < 2 ^ w.sum := by
  exact Nat.sub_pos_iff_lt.mp hD

/-- The rotation identity can equivalently take candidate D>0 as input. -/
theorem affine_constant_rotation_of_denominator_pos (a : ℕ) (as : List ℕ)
    (hD : 0 < 2 ^ (a + as.sum) - 3 ^ (as.length + 1)) :
    2 ^ a * syracuseAffineConstant (as ++ [a]) =
      3 * syracuseAffineConstant (a :: as) +
        (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
  exact affine_constant_rotation a as (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hD))

/-- Any nonempty word has positive canonical affine constant, even if some
or all of its entries are zero. -/
theorem affine_constant_cons_pos (a : ℕ) (as : List ℕ) :
    0 < syracuseAffineConstant (a :: as) := by
  rw [syracuseAffineConstant]
  have hthree : 0 < (3 : ℕ) ^ as.length :=
    Nat.pow_pos_iff.mpr (Or.inl (by norm_num : 0 < (3 : ℕ)))
  omega

theorem affine_constant_pos_of_nonempty (w : List ℕ) (hne : w ≠ []) :
    0 < syracuseAffineConstant w := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons a as => exact affine_constant_cons_pos a as

/-- A positive head exponent makes the canonical numerator odd; positivity
of the other exponents is not required for this fact. -/
theorem affine_constant_odd_of_head_pos (a : ℕ) (as : List ℕ) (ha : 0 < a) :
    Odd (syracuseAffineConstant (a :: as)) := by
  rw [syracuseAffineConstant]
  exact Odd.add_even (three_pow_odd as.length)
    (Even.mul_right (two_pow_even a ha) (syracuseAffineConstant as))

/-- A positive head and positive candidate denominator suffice for odd D.
The needed gap is derived from D>0, never from an unconstructed cycle. -/
theorem affine_denominator_odd_of_pos (a : ℕ) (as : List ℕ) (ha : 0 < a)
    (hD : 0 < 2 ^ (a + as.sum) - 3 ^ (as.length + 1)) :
    Odd (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
  have hK : 0 < a + as.sum := by omega
  have hgap : 3 ^ (as.length + 1) < 2 ^ (a + as.sum) := Nat.sub_pos_iff_lt.mp hD
  exact Nat.Even.sub_odd (Nat.le_of_lt hgap)
    (two_pow_even (a + as.sum) hK) (three_pow_odd (as.length + 1))

/-- One-step divisibility transport with an honest explicit odd-D premise.
Oddness supplies coprimality with the dyadic multiplier. -/
theorem affine_constant_rotation_dvd (a : ℕ) (as : List ℕ)
    (hgap : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum))
    (hodd : Odd (2 ^ (a + as.sum) - 3 ^ (as.length + 1)))
    (hdiv : (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) ∣
      syracuseAffineConstant (a :: as)) :
    (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) ∣
      syracuseAffineConstant (as ++ [a]) := by
  let D : ℕ := 2 ^ (a + as.sum) - 3 ^ (as.length + 1)
  have hcop : Nat.Coprime D (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  obtain ⟨k, hk⟩ := hdiv
  have hmul : D ∣ 2 ^ a * syracuseAffineConstant (as ++ [a]) := by
    refine ⟨3 * k + 1, ?_⟩
    calc
      2 ^ a * syracuseAffineConstant (as ++ [a]) =
          3 * syracuseAffineConstant (a :: as) + D := affine_constant_rotation a as hgap
      _ = D * (3 * k + 1) := by
        rw [hk]
        ring
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hmul

private theorem affine_constant_rotate_one_dvd (w : List ℕ)
    (hgap : 3 ^ w.length ≤ 2 ^ w.sum)
    (hodd : Odd (2 ^ w.sum - 3 ^ w.length))
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate 1) := by
  cases w with
  | nil =>
      simp [syracuseAffineConstant]
  | cons a as =>
      have hgap' : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum) := by
        simpa only [List.length_cons, List.sum_cons] using hgap
      have hodd' : Odd (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) := by
        simpa only [List.length_cons, List.sum_cons] using hodd
      have hdiv' : (2 ^ (a + as.sum) - 3 ^ (as.length + 1)) ∣
          syracuseAffineConstant (a :: as) := by
        simpa only [List.length_cons, List.sum_cons] using hdiv
      simpa only [List.length_cons, List.sum_cons, List.rotate_cons_succ,
        List.rotate_zero] using affine_constant_rotation_dvd a as hgap' hodd' hdiv'

/-- All rotations preserve the same denominator because length and sum are
invariant. This stronger version needs no positivity assumptions on entries:
the arithmetic gap and odd denominator remain explicit hypotheses. -/
theorem affine_constant_rotate_dvd_of_odd_denominator (w : List ℕ)
    (hgap : 3 ^ w.length ≤ 2 ^ w.sum)
    (hodd : Odd (2 ^ w.sum - 3 ^ w.length))
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (j : ℕ) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate j) := by
  induction j with
  | zero =>
      simpa only [List.rotate_zero] using hdiv
  | succ j ih =>
      have hsum : (w.rotate j).sum = w.sum :=
        List.Perm.sum_eq (List.rotate_perm w j)
      have hgapR : 3 ^ (w.rotate j).length ≤ 2 ^ (w.rotate j).sum := by
        simpa only [List.length_rotate, hsum] using hgap
      have hoddR : Odd (2 ^ (w.rotate j).sum - 3 ^ (w.rotate j).length) := by
        simpa only [List.length_rotate, hsum] using hodd
      have hdivR : (2 ^ (w.rotate j).sum - 3 ^ (w.rotate j).length) ∣
          syracuseAffineConstant (w.rotate j) := by
        simpa only [List.length_rotate, hsum] using ih
      have hnext := affine_constant_rotate_one_dvd (w.rotate j) hgapR hoddR hdivR
      simpa only [List.length_rotate, hsum, List.rotate_rotate] using hnext

/-- Positivity of entries is invariant under every rotation. This is useful
for subsequent quotient-state work, but asserts no quotient or cycle here. -/
theorem rotate_positive_entries (w : List ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a) (j : ℕ) :
    ∀ a : ℕ, a ∈ w.rotate j → 0 < a := by
  intro a ha
  exact hpos a (List.mem_rotate.mp ha)

/-- Noncircular positive-word interface: a nonempty positive word with an
explicit strict arithmetic gap and divisibility has divisible canonical
numerator at every rotation. No actual-cycle theorem or realization is used. -/
theorem affine_constant_rotate_dvd (w : List ℕ) (hne : w ≠ [])
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (j : ℕ) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate j) := by
  have hodd : Odd (2 ^ w.sum - 3 ^ w.length) := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons a as =>
        have ha : 0 < a := hpos a (by simp)
        have hD : 0 < 2 ^ (a + as.sum) - 3 ^ (as.length + 1) := by
          apply Nat.sub_pos_iff_lt.mpr
          simpa only [List.length_cons, List.sum_cons] using hgap
        simpa only [List.length_cons, List.sum_cons] using
          affine_denominator_odd_of_pos a as ha hD
  exact affine_constant_rotate_dvd_of_odd_denominator w (Nat.le_of_lt hgap) hodd hdiv j

end CollatzAffineWordRotationDraft01

namespace CollatzSyracuseCandidateWordRealizationDraft01

open CollatzAffineWordRotationDraft01

/-- A scaled edge with a positive odd target gives both the actual accelerated
step and the exact removed exponent. No cycle is presumed in this helper. -/
private theorem step_and_valuation_of_scaled_edge (x y a : ℕ)
    (hypos : 0 < y) (hyodd : Odd y)
    (hscaled : 2 ^ a * y = 3 * x + 1) :
    syracuseStep x = y ∧ (3 * x + 1).factorization 2 = a := by
  have hnot : ¬2 ∣ y := Odd.not_two_dvd_nat hyodd
  constructor
  · unfold syracuseStep
    rw [← hscaled]
    exact Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two hnot
  · have hpow : 2 ^ a ≠ 0 := Nat.ne_of_gt
      (Nat.pow_pos_iff.mpr (Or.inl (by norm_num : 0 < (2 : ℕ))))
    rw [← hscaled, Nat.factorization_mul hpow (Nat.ne_of_gt hypos),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hnot, Nat.add_zero]

/-- The canonical quotient realizes the whole supplied word as an actual
Syracuse return. The period need not be least; repeated states are retained. -/
theorem syracuse_candidate_word_realization_at_quotient (w : List ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    let m : ℕ := syracuseAffineConstant w / (2 ^ w.sum - 3 ^ w.length);
    0 < m ∧ syracuseStep^[w.length] m = m ∧
      List.ofFn (fun i : Fin w.length =>
        (3 * syracuseStep^[i.val] m + 1).factorization 2) = w := by
  have hne : w ≠ [] := by
    intro hnil
    simp [hnil] at hgap
  have hp : 0 < w.length := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons a as => exact Nat.succ_pos as.length
  let D : ℕ := 2 ^ w.sum - 3 ^ w.length
  have hD : 0 < D := Nat.sub_pos_iff_lt.mpr hgap
  let N : ℕ → ℕ := fun j => syracuseAffineConstant (w.rotate j) / D
  have hrotne : ∀ j : ℕ, w.rotate j ≠ [] := by
    intro j hnil
    exact hne (List.rotate_eq_nil_iff.mp hnil)
  have hdecomp : ∀ j : ℕ, ∃ a : ℕ, ∃ as : List ℕ, w.rotate j = a :: as := by
    intro j
    cases hr : w.rotate j with
    | nil => exact False.elim (hrotne j hr)
    | cons a as => exact ⟨a, as, rfl⟩
  have hCpos : ∀ j : ℕ, 0 < syracuseAffineConstant (w.rotate j) := by
    intro j
    exact affine_constant_pos_of_nonempty (w.rotate j) (hrotne j)
  have hCodd : ∀ j : ℕ, Odd (syracuseAffineConstant (w.rotate j)) := by
    intro j
    obtain ⟨a, as, hr⟩ := hdecomp j
    have hamem : a ∈ w.rotate j := by
      rw [hr]
      simp
    have ha : 0 < a := hpos a (List.mem_rotate.mp hamem)
    rw [hr]
    exact affine_constant_odd_of_head_pos a as ha
  have hdivrot : ∀ j : ℕ, D ∣ syracuseAffineConstant (w.rotate j) := by
    intro j
    exact affine_constant_rotate_dvd w hne hpos hgap hdiv j
  have hmul : ∀ j : ℕ, D * N j = syracuseAffineConstant (w.rotate j) := by
    intro j
    change D * (syracuseAffineConstant (w.rotate j) / D) =
      syracuseAffineConstant (w.rotate j)
    exact Nat.mul_div_cancel' (hdivrot j)
  have hNpos : ∀ j : ℕ, 0 < N j := by
    intro j
    have hC := hCpos j
    have hm := hmul j
    by_contra h
    have hz : N j = 0 := by omega
    rw [hz, Nat.mul_zero] at hm
    omega
  have hNodd : ∀ j : ℕ, Odd (N j) := by
    intro j
    have hproduct : Odd (D * N j) := by
      rw [hmul j]
      exact hCodd j
    exact (Nat.odd_mul.mp hproduct).2
  have hedge : ∀ j : ℕ, ∃ a : ℕ, ∃ as : List ℕ,
      w.rotate j = a :: as ∧ 2 ^ a * N (j + 1) = 3 * N j + 1 := by
    intro j
    obtain ⟨a, as, hr⟩ := hdecomp j
    refine ⟨a, as, hr, ?_⟩
    have hlength : as.length + 1 = w.length := by
      simpa only [hr, List.length_cons] using List.length_rotate w j
    have hsum : a + as.sum = w.sum := by
      simpa only [hr, List.sum_cons] using List.Perm.sum_eq (List.rotate_perm w j)
    have hgapA : 3 ^ (as.length + 1) ≤ 2 ^ (a + as.sum) := by
      rw [hlength, hsum]
      exact Nat.le_of_lt hgap
    have hDexpr : D = 2 ^ (a + as.sum) - 3 ^ (as.length + 1) := by
      change 2 ^ w.sum - 3 ^ w.length = 2 ^ (a + as.sum) - 3 ^ (as.length + 1)
      rw [hlength, hsum]
    have hrnext : w.rotate (j + 1) = as ++ [a] := by
      calc
        w.rotate (j + 1) = (w.rotate j).rotate 1 := (List.rotate_rotate w j 1).symm
        _ = (a :: as).rotate 1 := by rw [hr]
        _ = as ++ [a] := by
          simp only [List.rotate_cons_succ, List.rotate_zero]
    have hscaled : D * (2 ^ a * N (j + 1)) = D * (3 * N j + 1) := by
      calc
        D * (2 ^ a * N (j + 1)) = 2 ^ a * (D * N (j + 1)) := by ring
        _ = 2 ^ a * syracuseAffineConstant (w.rotate (j + 1)) := by rw [hmul (j + 1)]
        _ = 2 ^ a * syracuseAffineConstant (as ++ [a]) := by rw [hrnext]
        _ = 3 * syracuseAffineConstant (a :: as) + D := by
          simpa only [hDexpr] using affine_constant_rotation a as hgapA
        _ = 3 * syracuseAffineConstant (w.rotate j) + D := by rw [hr]
        _ = 3 * (D * N j) + D := by rw [hmul j]
        _ = D * (3 * N j + 1) := by ring
    exact Nat.eq_of_mul_eq_mul_left hD hscaled
  have hstep : ∀ j : ℕ, syracuseStep (N j) = N (j + 1) := by
    intro j
    obtain ⟨a, as, hr, he⟩ := hedge j
    exact (step_and_valuation_of_scaled_edge (N j) (N (j + 1)) a
      (hNpos (j + 1)) (hNodd (j + 1)) he).1
  have hiter : ∀ j : ℕ, syracuseStep^[j] (N 0) = N j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        simpa only [Function.iterate_succ_apply', ih] using hstep j
  have hperiod : N w.length = N 0 := by
    dsimp only [N]
    rw [List.rotate_length, List.rotate_zero]
  have hcycle : syracuseStep^[w.length] (N 0) = N 0 :=
    (hiter w.length).trans hperiod
  have hval : ∀ i : Fin w.length,
      (3 * syracuseStep^[i.val] (N 0) + 1).factorization 2 = w[i.val]'i.isLt := by
    intro i
    obtain ⟨a, as, hr, he⟩ := hedge i.val
    have hv : (3 * N i.val + 1).factorization 2 = a :=
      (step_and_valuation_of_scaled_edge (N i.val) (N (i.val + 1)) a
        (hNpos (i.val + 1)) (hNodd (i.val + 1)) he).2
    have hzero : 0 < (w.rotate i.val).length := by
      rw [List.length_rotate]
      exact hp
    have hhead : (w.rotate i.val)[0]'hzero = a := by
      simp [hr, List.getElem_cons]
    have hindex : (w.rotate i.val)[0]'hzero = w[i.val]'i.isLt := by
      simpa only [Nat.zero_add, Nat.mod_eq_of_lt i.isLt] using
        List.getElem_rotate w i.val 0 hzero
    calc
      (3 * syracuseStep^[i.val] (N 0) + 1).factorization 2 =
          (3 * N i.val + 1).factorization 2 := by rw [hiter i.val]
      _ = a := hv
      _ = w[i.val]'i.isLt := hhead.symm.trans hindex
  have hword : List.ofFn (fun i : Fin w.length =>
      (3 * syracuseStep^[i.val] (N 0) + 1).factorization 2) = w := by
    calc
      List.ofFn (fun i : Fin w.length =>
          (3 * syracuseStep^[i.val] (N 0) + 1).factorization 2) =
          List.ofFn (fun i : Fin w.length => w[i.val]'i.isLt) :=
        congrArg (fun f : Fin w.length → ℕ => List.ofFn f) (funext hval)
      _ = w := List.ofFn_getElem (xs := w)
  have hseed : N 0 = syracuseAffineConstant w / D := by
    simp only [N, List.rotate_zero]
  change 0 < syracuseAffineConstant w / D ∧
    syracuseStep^[w.length] (syracuseAffineConstant w / D) = syracuseAffineConstant w / D ∧
    List.ofFn (fun i : Fin w.length =>
      (3 * syracuseStep^[i.val] (syracuseAffineConstant w / D) + 1).factorization 2) = w
  rw [← hseed]
  exact ⟨hNpos 0, hcycle, hword⟩

/-- Clean first converse: the supplied arithmetic integrality conditions
realize w as the exact valuation list of a positive Syracuse-periodic point.
No least-period or primitive-word conclusion is asserted. -/
theorem syracuse_candidate_word_realization (w : List ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    ∃ m : ℕ, 0 < m ∧ syracuseStep^[w.length] m = m ∧
      List.ofFn (fun i : Fin w.length =>
        (3 * syracuseStep^[i.val] m + 1).factorization 2) = w := by
  refine ⟨syracuseAffineConstant w / (2 ^ w.sum - 3 ^ w.length), ?_⟩
  exact syracuse_candidate_word_realization_at_quotient w hpos hgap hdiv

end CollatzSyracuseCandidateWordRealizationDraft01

theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  by_cases hbudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length
  · exact syracuse_primitive_word_affine_nondivisibility_with_baseline_budget
      w hpositive hlength hprimitive hgap hlow hlowSharp hbudget
  · intro hdiv
    obtain ⟨m, hm, hcycle, hword⟩ :=
      CollatzSyracuseCandidateWordRealizationDraft01.syracuse_candidate_word_realization
        w hpositive hgap hdiv
    have hsum : (∑ i ∈ Finset.range w.length,
        (3 * syracuseStep^[i] m + 1).factorization 2) = w.sum := by
      rw [Finset.sum_range (fun i : ℕ =>
        (3 * syracuseStep^[i] m + 1).factorization 2)]
      simpa only [List.sum_ofFn] using
        congrArg (fun l : List ℕ => l.sum) hword
    have hbelow : ∀ y : ℕ, 0 < y → syracuseStep^[w.length] y = y →
        y < 2310000 → y = 1 := by
      intro y hy hreturn hyB
      exact syracuse_no_cycle_below_2310000 y w.length hy
        (by omega) (by omega) hreturn
    have hviolation : (3 * 2310000 + 1 : ℕ) ^ w.length <
        (2 : ℕ) ^ (∑ i ∈ Finset.range w.length,
          (3 * syracuseStep^[i] m + 1).factorization 2) *
          (2310000 : ℕ) ^ w.length := by
      rw [hsum]
      omega
    have hmone : m = 1 :=
      syracuse_cycle_eq_one_of_state_baseline_budget_violation
        2310000 m w.length hm (by omega) hcycle hbelow hviolation
    have hfixed : syracuseStep 1 = 1 := by decide +kernel
    have hvaluation : ∀ i : ℕ,
        (3 * syracuseStep^[i] m + 1).factorization 2 = 2 := by
      intro i
      rw [hmone, Function.iterate_fixed hfixed i]
      decide +kernel
    have hsumTwo : w.sum = 2 * w.length := by
      calc
        w.sum = ∑ i ∈ Finset.range w.length,
            (3 * syracuseStep^[i] m + 1).factorization 2 := hsum.symm
        _ = ∑ _i ∈ Finset.range w.length, 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact hvaluation i
        _ = 2 * w.length := by simp [Nat.nsmul_eq_mul, Nat.mul_comm]
    omega
