-- Prove2me | solution 1 for syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306
-- status  : ACCEPTED   (prove)
-- author  : @FakeMink
-- created : 2026-10-01T22:55:11.463985+00:00
-- url     : https://prove2.me/submissions/8b4d8157-4087-4099-acd1-6886fd04c8c2

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_min_upper_bound
import Theorems.Thm_syracuse_no_cycle_below_2310000
import Theorems.Thm_syracuse_periodic_reaches_one

set_option autoImplicit false

open scoped BigOperators

namespace CollatzTailThreshold485Over306

-- A closed natural-number certificate reduced by the Lean kernel.
set_option maxRecDepth 100000 in
private theorem mean_margin_certificate :
    (3 * 2310000 + 1 : ℕ) ^ 306 <
      (2 : ℕ) ^ 485 * (2310000 : ℕ) ^ 306 := by
  decide +kernel

private theorem mean_margin_above_baseline (m : ℕ)
    (hm : 0 < m) (hb : 2310000 ≤ m) :
    (3 * m + 1) ^ 306 < (2 : ℕ) ^ 485 * m ^ 306 := by
  have hratio : (3 * m + 1) * 2310000 ≤ (3 * 2310000 + 1) * m := by
    nlinarith only [hb]
  have hscaled :
      (3 * m + 1) ^ 306 * (2310000 : ℕ) ^ 306 <
        ((2 : ℕ) ^ 485 * m ^ 306) * (2310000 : ℕ) ^ 306 := by
    calc
      (3 * m + 1) ^ 306 * (2310000 : ℕ) ^ 306 =
          ((3 * m + 1) * 2310000) ^ 306 := (mul_pow _ _ _).symm
      _ ≤ ((3 * 2310000 + 1) * m) ^ 306 :=
        Nat.pow_le_pow_left hratio 306
      _ = (3 * 2310000 + 1 : ℕ) ^ 306 * m ^ 306 := mul_pow _ _ _
      _ < ((2 : ℕ) ^ 485 * (2310000 : ℕ) ^ 306) * m ^ 306 :=
        Nat.mul_lt_mul_of_pos_right mean_margin_certificate (Nat.pow_pos hm)
      _ = ((2 : ℕ) ^ 485 * m ^ 306) * (2310000 : ℕ) ^ 306 := by
        exact Nat.mul_right_comm ((2 : ℕ) ^ 485) ((2310000 : ℕ) ^ 306) (m ^ 306)
  exact Nat.lt_of_mul_lt_mul_right hscaled

-- The given minimum covers just one period. Periodicity supplies the minimum
-- over every natural index required by the imported public upper-bound theorem.
private theorem minimum_all_indices (m p : ℕ) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ i : ℕ, i < p → m ≤ syracuseStep^[i] m) :
    ∀ i : ℕ, m ≤ syracuseStep^[i] m := by
  have hperiodic : Function.IsPeriodicPt syracuseStep p m := hcyc
  intro i
  calc
    m ≤ syracuseStep^[i % p] m := hmin (i % p) (Nat.mod_lt i hp)
    _ = syracuseStep^[i] m :=
      Function.IsPeriodicPt.iterate_mod_apply hperiodic i

-- High mean excludes nontrivial cycles represented at their minimum.
theorem syracuse_mean_valuation_ge_485_over_306_eq_one (m p : ℕ)
    (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ i : ℕ, i < p → m ≤ syracuseStep^[i] m)
    (hhigh : 485 * p ≤
      306 * (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] m + 1).factorization 2)) :
    m = 1 := by
  by_cases hsmall : m ≤ 2309999
  · exact syracuse_no_cycle_below_2310000 m p hm hp hsmall hcyc
  have hb : 2310000 ≤ m := by omega
  have hminAll : ∀ i : ℕ, m ≤ syracuseStep^[i] m :=
    minimum_all_indices m p hp hcyc hmin
  let A : ℕ := ∑ i ∈ Finset.range p,
    (3 * syracuseStep^[i] m + 1).factorization 2
  have hupper : (2 : ℕ) ^ A * m ^ p ≤ (3 * m + 1) ^ p :=
    syracuse_cycle_min_upper_bound m p hm hp hcyc hminAll
  have hhighA : 485 * p ≤ 306 * A := hhigh
  have hupper306 :
      ((2 : ℕ) ^ A * m ^ p) ^ 306 ≤ ((3 * m + 1) ^ p) ^ 306 :=
    Nat.pow_le_pow_left hupper 306
  have hpower :
      ((2 : ℕ) ^ 485 * m ^ 306) ^ p ≤ ((3 * m + 1) ^ 306) ^ p := by
    calc
      ((2 : ℕ) ^ 485 * m ^ 306) ^ p =
          (2 : ℕ) ^ (485 * p) * m ^ (306 * p) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (2 : ℕ) ^ (306 * A) * m ^ (306 * p) :=
        Nat.mul_le_mul_right (m ^ (306 * p))
          (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hhighA)
      _ = ((2 : ℕ) ^ A * m ^ p) ^ 306 := by
        simp only [mul_pow, ← pow_mul, Nat.mul_comm]
      _ ≤ ((3 * m + 1) ^ p) ^ 306 := hupper306
      _ = ((3 * m + 1) ^ 306) ^ p :=
        pow_right_comm (3 * m + 1) p 306
  have hreverse : (2 : ℕ) ^ 485 * m ^ 306 ≤ (3 * m + 1) ^ 306 :=
    (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (ne_of_gt hp)).mp hpower
  have hstrict : (3 * m + 1) ^ 306 < (2 : ℕ) ^ 485 * m ^ 306 :=
    mean_margin_above_baseline m hm hb
  exact False.elim ((not_le_of_gt hstrict) hreverse)

end CollatzTailThreshold485Over306

namespace CollatzTailThresholdMinimumBridge

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
Its minimum hypothesis concerns every state in the first p positions; these
are a full period. The proof below actually constructs a minimum over all
forward iterates, so no minimum-position or cyclic-count assumption is hidden. -/
theorem high_mean_of_cycle_minimum_criterion (p : ℕ) (hp : 0 < p)
    (hcriterion : ∀ y : ℕ, 0 < y → syracuseStep^[p] y = y →
      (∀ i : ℕ, i < p → y ≤ syracuseStep^[i] y) →
      485 * p ≤ 306 * (∑ i ∈ Finset.range p,
        (3 * syracuseStep^[i] y + 1).factorization 2) → y = 1)
    (m : ℕ) (hm : 0 < m) (hcycle : syracuseStep^[p] m = m)
    (hmean : 485 * p ≤ 306 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2)) :
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
  have hmeanY : 485 * p ≤ 306 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] y + 1).factorization 2) := by
    rw [hsum]
    exact hmean
  have hyone : y = 1 :=
    hcriterion y hypos hycycle (fun i _ => hminimum i) hmeanY
  exact syracuse_periodic_reaches_one m p hp hcycle ⟨j, hjy.trans hyone⟩

end CollatzTailThresholdMinimumBridge

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hhigh : 485 * p ≤ 306 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2)) :
    m = 1 := by
  exact CollatzTailThresholdMinimumBridge.high_mean_of_cycle_minimum_criterion
    p hp
    (fun y hy hreturn hminimum hvaluation =>
      CollatzTailThreshold485Over306.syracuse_mean_valuation_ge_485_over_306_eq_one
        y p hy hp hreturn hminimum hvaluation)
    m hm hcyc hhigh

