-- Prove2me | solution 1 for syracuse_cycle_eq_one_of_state_baseline_budget_violation
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-02T03:35:51.74274+00:00
-- url     : https://prove2.me/submissions/ff328a96-0ac7-458d-9fbb-250e6bf8dea5

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_min_upper_bound
import Theorems.Thm_syracuse_periodic_reaches_one

set_option autoImplicit false

open scoped BigOperators

namespace CollatzExactBaselineBudget

-- The baseline is an explicit logical premise, not a claimed finite certificate.
theorem minimum_budget_violation_eq_one (B m p : ℕ)
    (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ i : ℕ, m ≤ syracuseStep^[i] m)
    (hbelow : ∀ y : ℕ, 0 < y → syracuseStep^[p] y = y → y < B → y = 1)
    (hviolation : (3 * B + 1) ^ p <
      (2 : ℕ) ^ (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2) * B ^ p) :
    m = 1 := by
  by_cases hsmall : m < B
  · exact hbelow m hm hcyc hsmall
  have hb : B ≤ m := by omega
  let K : ℕ := ∑ i ∈ Finset.range p,
    (3 * syracuseStep^[i] m + 1).factorization 2
  have hupper : (2 : ℕ) ^ K * m ^ p ≤ (3 * m + 1) ^ p :=
    syracuse_cycle_min_upper_bound m p hm hp hcyc hmin
  have hratio : (3 * m + 1) * B ≤ (3 * B + 1) * m := by
    nlinarith only [hb]
  have hscaled : ((2 : ℕ) ^ K * B ^ p) * m ^ p ≤
      (3 * B + 1) ^ p * m ^ p := by
    calc
      ((2 : ℕ) ^ K * B ^ p) * m ^ p =
          ((2 : ℕ) ^ K * m ^ p) * B ^ p :=
        Nat.mul_right_comm ((2 : ℕ) ^ K) (B ^ p) (m ^ p)
      _ ≤ (3 * m + 1) ^ p * B ^ p :=
        Nat.mul_le_mul_right (B ^ p) hupper
      _ = ((3 * m + 1) * B) ^ p := (mul_pow _ _ _).symm
      _ ≤ ((3 * B + 1) * m) ^ p := Nat.pow_le_pow_left hratio p
      _ = (3 * B + 1) ^ p * m ^ p := mul_pow _ _ _
  have hreverse : (3 * B + 1) ^ p * m ^ p <
      ((2 : ℕ) ^ K * B ^ p) * m ^ p :=
    Nat.mul_lt_mul_of_pos_right hviolation (Nat.pow_pos hm)
  exact False.elim ((not_le_of_gt hreverse) hscaled)

end CollatzExactBaselineBudget

namespace CollatzExactBudgetMinimumBridge

private theorem syracuse_positive (n : ℕ) : 0 < syracuseStep n := by
  unfold syracuseStep
  exact Nat.ordCompl_pos 2 (by omega : 3 * n + 1 ≠ 0)

private theorem iterate_positive (f : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < f n)
    (m : ℕ) (hm : 0 < m) (t : ℕ) : 0 < f^[t] m := by
  induction t with
  | zero => simpa using hm
  | succ t ih =>
      simpa only [Function.iterate_succ_apply'] using hpos (f^[t] m) ih

private theorem periodic_iterate {f : ℕ → ℕ} {m p : ℕ}
    (hcycle : f^[p] m = m) (j : ℕ) :
    f^[p] (f^[j] m) = f^[j] m := by
  calc
    f^[p] (f^[j] m) = f^[p + j] m := (Function.iterate_add_apply f p j m).symm
    _ = f^[j + p] m := by rw [Nat.add_comm]
    _ = f^[j] (f^[p] m) := Function.iterate_add_apply f j p m
    _ = f^[j] m := by rw [hcycle]

/-- Every forward orbit point has a representative in the first p positions.
The identity itself is valid for p=0; positivity is needed only for mod_lt. -/
private theorem iterate_mod_of_return {f : ℕ → ℕ} {m p : ℕ}
    (hcycle : f^[p] m = m) (t : ℕ) :
    f^[t] m = f^[t % p] m := by
  have hmultiple : f^[p * (t / p)] m = m := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hcycle (t / p)
  calc
    f^[t] m = f^[t % p + p * (t / p)] m := by rw [Nat.mod_add_div]
    _ = f^[t % p] (f^[p * (t / p)] m) :=
      Function.iterate_add_apply f (t % p) (p * (t / p)) m
    _ = f^[t % p] m := by rw [hmultiple]

/-- A whole-period sum is invariant under any shift of a periodic Nat-valued
sequence. This is additive cancellation, not a word-symmetry assumption. -/
private theorem sum_range_shift_of_period (g : ℕ → ℕ) (p : ℕ)
    (hperiod : ∀ i : ℕ, g (i + p) = g i) (j : ℕ) :
    (∑ i ∈ Finset.range p, g (i + j)) = (∑ i ∈ Finset.range p, g i) := by
  have hleftShift : (∑ i ∈ Finset.range j, g (p + i)) =
      (∑ i ∈ Finset.range j, g i) := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      g (p + i) = g (i + p) := congrArg g (Nat.add_comm p i)
      _ = g i := hperiod i
  have hrightShift : (∑ i ∈ Finset.range p, g (j + i)) =
      (∑ i ∈ Finset.range p, g (i + j)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg g (Nat.add_comm j i)
  have hleft := Finset.sum_range_add g p j
  have hright := Finset.sum_range_add g j p
  rw [hleftShift] at hleft
  rw [hrightShift] at hright
  have hcancel :
      (∑ i ∈ Finset.range p, g i) + (∑ i ∈ Finset.range j, g i) =
        (∑ i ∈ Finset.range j, g i) + (∑ i ∈ Finset.range p, g (i + j)) := by
    calc
      (∑ i ∈ Finset.range p, g i) + (∑ i ∈ Finset.range j, g i) =
          (∑ i ∈ Finset.range (p + j), g i) := hleft.symm
      _ = (∑ i ∈ Finset.range (j + p), g i) := by rw [Nat.add_comm p j]
      _ = (∑ i ∈ Finset.range j, g i) +
          (∑ i ∈ Finset.range p, g (i + j)) := hright
  have hcancel' :
      (∑ i ∈ Finset.range j, g i) + (∑ i ∈ Finset.range p, g i) =
        (∑ i ∈ Finset.range j, g i) + (∑ i ∈ Finset.range p, g (i + j)) :=
    (Nat.add_comm _ _).trans hcancel
  exact (Nat.add_left_cancel hcancel').symm

/-- The actual full-cycle two-adic valuation sum is invariant under any
forward shift. Only the return equality is used; no minimality, mean, or
valuation-word symmetry hypothesis is needed. -/
theorem valuation_sum_shift (m p j : ℕ) (hcycle : syracuseStep^[p] m = m) :
    (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] (syracuseStep^[j] m) + 1).factorization 2) =
      (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) := by
  let g : ℕ → ℕ := fun i => (3 * syracuseStep^[i] m + 1).factorization 2
  have hperiod : ∀ i : ℕ, g (i + p) = g i := by
    intro i
    dsimp [g]
    rw [Function.iterate_add_apply, hcycle]
  calc
    (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] (syracuseStep^[j] m) + 1).factorization 2) =
        (∑ i ∈ Finset.range p, g (i + j)) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [g]
      exact congrArg (fun n : ℕ => (3 * n + 1).factorization 2)
        (Function.iterate_add_apply syracuseStep i j m).symm
    _ = (∑ i ∈ Finset.range p, g i) := sum_range_shift_of_period g p hperiod j
    _ = (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) := rfl

/-- Conditional bridge: hcriterion is an explicit logical parameter.
Its minimum hypothesis covers every forward iterate. The proof constructs
that minimum from the first p positions using periodicity, so no starting
minimum or cyclic-count assumption is hidden. -/
theorem of_cycle_minimum_budget_criterion (B p : ℕ) (hp : 0 < p)
    (hcriterion : ∀ y : ℕ, 0 < y → syracuseStep^[p] y = y →
      (∀ i : ℕ, y ≤ syracuseStep^[i] y) →
      (3 * B + 1) ^ p < (2 : ℕ) ^ (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] y + 1).factorization 2) * B ^ p → y = 1)
    (m : ℕ) (hm : 0 < m) (hcycle : syracuseStep^[p] m = m)
    (hbudget : (3 * B + 1) ^ p < (2 : ℕ) ^ (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) * B ^ p) :
    m = 1 := by
  classical
  let s : Finset ℕ := (Finset.range p).image (fun i : ℕ => syracuseStep^[i] m)
  have hs : s.Nonempty := by
    refine ⟨syracuseStep^[0] m, ?_⟩
    change syracuseStep^[0] m ∈ (Finset.range p).image (fun i : ℕ => syracuseStep^[i] m)
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩
  let y : ℕ := s.min' hs
  have hymem : y ∈ s := Finset.min'_mem s hs
  change y ∈ (Finset.range p).image (fun i : ℕ => syracuseStep^[i] m) at hymem
  obtain ⟨j, hjmem, hjy⟩ := Finset.mem_image.mp hymem
  have hjp : j < p := Finset.mem_range.mp hjmem
  have hypos : 0 < y := by
    rw [← hjy]
    exact iterate_positive syracuseStep (fun n _ => syracuse_positive n) m hm j
  have hycycle : syracuseStep^[p] y = y := by
    rw [← hjy]
    exact periodic_iterate hcycle j
  have hminOriginal : ∀ i : ℕ, i < p → y ≤ syracuseStep^[i] m := by
    intro i hi
    have himem : syracuseStep^[i] m ∈ s := by
      change syracuseStep^[i] m ∈ (Finset.range p).image (fun k : ℕ => syracuseStep^[k] m)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
    exact Finset.min'_le s (syracuseStep^[i] m) himem
  have hminimum : ∀ i : ℕ, y ≤ syracuseStep^[i] y := by
    intro i
    have hi : (i + j) % p < p := Nat.mod_lt _ hp
    calc
      y ≤ syracuseStep^[(i + j) % p] m := hminOriginal _ hi
      _ = syracuseStep^[i + j] m := (iterate_mod_of_return hcycle (i + j)).symm
      _ = syracuseStep^[i] (syracuseStep^[j] m) :=
        Function.iterate_add_apply syracuseStep i j m
      _ = syracuseStep^[i] y := by rw [hjy]
  have hsum : (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] y + 1).factorization 2) =
      (∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) := by
    rw [← hjy]
    exact valuation_sum_shift m p j hcycle
  have hbudgetY : (3 * B + 1) ^ p < (2 : ℕ) ^ (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] y + 1).factorization 2) * B ^ p := by
    rw [hsum]
    exact hbudget
  have hyone : y = 1 :=
    hcriterion y hypos hycycle hminimum hbudgetY
  exact syracuse_periodic_reaches_one m p hp hcycle ⟨j, hjy.trans hyone⟩

end CollatzExactBudgetMinimumBridge

theorem solution (B m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hbelow : ∀ y : ℕ, 0 < y → syracuseStep^[p] y = y → y < B → y = 1)
    (hviolation : (3 * B + 1) ^ p <
      (2 : ℕ) ^ (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2) * B ^ p) :
    m = 1 := by
  exact CollatzExactBudgetMinimumBridge.of_cycle_minimum_budget_criterion
    B p hp
    (fun y hy hreturn hminimum hbudget =>
      CollatzExactBaselineBudget.minimum_budget_violation_eq_one
        B y p hy hp hreturn hminimum hbelow hbudget)
    m hm hcyc hviolation
