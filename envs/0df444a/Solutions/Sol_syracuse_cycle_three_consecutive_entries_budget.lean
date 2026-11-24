-- Prove2me | solution 1 for syracuse_cycle_three_consecutive_entries_budget
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:58:02.808825+00:00
-- url     : https://prove2.me/submissions/99fc352b-9f78-4a5d-b913-acf3fb477429

import Definitions.Def_syracuseStep
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/- If the two transitions divide by 2^e and 2^f, the three entries
   dominate 8b, 9b and 12b in one of the following orders. -/
private theorem tripleRanks (x y z e f b : ℕ)
    (hx : 8 * b ≤ x) (hy : 8 * b ≤ y) (hz : 8 * b ≤ z)
    (hxy : 2 ^ e * y = 3 * x + 1) (hyz : 2 ^ f * z = 3 * y + 1) :
    (9 * b ≤ x ∧ 12 * b ≤ y) ∨ (12 * b ≤ y ∧ 9 * b ≤ z) ∨
    (9 * b ≤ x ∧ 12 * b ≤ z) ∨ (12 * b ≤ x ∧ 9 * b ≤ y) := by
  by_cases he : e ≤ 1
  · have he2 : 2 ^ e ≤ 2 := Nat.pow_le_pow_right (by decide) he
    have h1 := Nat.mul_le_mul_right y he2
    have hbig : 12 * b ≤ y := by omega
    have htwo : 2 ^ (e + f) * z = 9 * x + 3 + 2 ^ e := by
      calc
        2 ^ (e + f) * z = 2 ^ e * (2 ^ f * z) := by rw [pow_add, Nat.mul_assoc]
        _ = 3 * (2 ^ e * y) + 2 ^ e := by rw [hyz]; ring
        _ = _ := by rw [hxy]; ring
    by_cases hef : e + f ≤ 3
    · have h8 : 2 ^ (e + f) ≤ 8 := Nat.pow_le_pow_right (by decide) hef
      have hlo : 9 * x ≤ 2 ^ (e + f) * z := by
        rw [htwo]
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      have h := hlo.trans (Nat.mul_le_mul_right z h8)
      exact Or.inr (Or.inl ⟨hbig, by omega⟩)
    · have h16 : 16 ≤ 2 ^ (e + f) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ e + f)
      have h := Nat.mul_le_mul_right z h16
      exact Or.inl ⟨by omega, hbig⟩
  · have he4 : 4 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ e)
    have h1 := Nat.mul_le_mul_right y he4
    by_cases hf : f ≤ 1
    · have hf2 : 2 ^ f ≤ 2 := Nat.pow_le_pow_right (by decide) hf
      have h2 := Nat.mul_le_mul_right z hf2
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · have hf4 : 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ f)
      have h2 := Nat.mul_le_mul_right z hf4
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

private theorem ratioBound {x b : ℕ} (h : b ≤ x) :
    (3 * x + 1) * b ≤ x * (3 * b + 1) := by
  simpa only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
    Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using Nat.add_le_add_left h (3 * x * b)

private theorem shiftProduct (v : ℕ → ℕ) (p : ℕ) (h : v p = v 0) (hv : 0 < v 0) :
    (∏ i ∈ Finset.range p, v (i + 1)) = ∏ i ∈ Finset.range p, v i := by
  apply Nat.eq_of_mul_eq_mul_right hv
  rw [← Finset.prod_range_succ', ← h, ← Finset.prod_range_succ]

theorem solution (m p b : ℕ) (hb : 0 < b) (hcycle : syracuseStep^[p] m = m)
    (hbase : ∀ i : ℕ, 8 * b ≤ syracuseStep^[i] m) :
    2 ^ (3 * ∑ i ∈ Finset.range p, (3 * syracuseStep^[i] m + 1).factorization 2) *
      ((8 * b) * (9 * b) * (12 * b)) ^ p ≤
        ((3 * (8 * b) + 1) * (3 * (9 * b) + 1) * (3 * (12 * b) + 1)) ^ p := by
  let x (i : ℕ) := syracuseStep^[i] m
  let g (i : ℕ) := 3 * x i + 1
  let e (i : ℕ) := (g i).factorization 2
  let R := Finset.range p
  let D := 8 * b * (9 * b) * (12 * b)
  let A := (3 * (8 * b) + 1) * (3 * (9 * b) + 1) * (3 * (12 * b) + 1)
  have hstep (i : ℕ) : 2 ^ e i * x (i + 1) = g i := by
    change 2 ^ (g i).factorization 2 * syracuseStep^[i + 1] m = g i
    rw [Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self (g i) 2
  have triple (i : ℕ) : g i * g (i + 1) * g (i + 2) * D ≤ x i * x (i + 1) * x (i + 2) * A := by
    obtain h | h | h | h := tripleRanks _ _ _ _ _ b (hbase i) (hbase (i + 1)) (hbase (i + 2))
      (hstep i) (hstep (i + 1))
    · simpa only [A, D, g, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul (Nat.mul_le_mul (ratioBound h.1) (ratioBound h.2)) (ratioBound (hbase (i + 2)))
    · simpa only [A, D, g, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul (Nat.mul_le_mul (ratioBound (hbase i)) (ratioBound h.1)) (ratioBound h.2)
    · simpa only [A, D, g, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul (Nat.mul_le_mul (ratioBound h.1) (ratioBound (hbase (i + 1)))) (ratioBound h.2)
    · simpa only [A, D, g, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul (Nat.mul_le_mul (ratioBound h.1) (ratioBound h.2)) (ratioBound (hbase (i + 2)))
  have hx : x p = x 0 := hcycle
  have hx1 : x (p + 1) = x 1 := by
    change syracuseStep^[p + 1] m = syracuseStep m
    rw [Function.iterate_succ_apply', hcycle]
  have xpos (i : ℕ) : 0 < x i := by have := hbase i; change 0 < syracuseStep^[i] m; omega
  have sx := shiftProduct x p hx (xpos 0)
  have sx2 := (shiftProduct (fun i => x (i + 1)) p hx1 (xpos 1)).trans sx
  have sg := shiftProduct g p (congrArg (fun z => 3 * z + 1) hx) (by dsimp [g]; omega)
  have sg2 := (shiftProduct (fun i => g (i + 1)) p (congrArg (fun z => 3 * z + 1) hx1)
    (by dsimp [g]; omega)).trans sg
  have hprod : (∏ i ∈ R, g i) = 2 ^ (∑ i ∈ R, e i) * ∏ i ∈ R, x i := by
    calc
      (∏ i ∈ R, g i) = ∏ i ∈ R, (2 ^ e i * x (i + 1)) :=
        Finset.prod_congr rfl (fun i _ => (hstep i).symm)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sx]
  have h := Finset.prod_le_prod' (s := Finset.range p) (fun i _ => triple i)
  change (∏ i ∈ Finset.range p, g i * g (i + 1) * g (i + 2) * D) ≤
    (∏ i ∈ Finset.range p, x i * x (i + 1) * x (i + 2) * A) at h
  change (∏ i ∈ Finset.range p, x (i + 2)) = _ at sx2
  change (∏ i ∈ Finset.range p, g (i + 2)) = _ at sg2
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, sx, sx2, sg, sg2] at h
  change (∏ i ∈ R, g i) * (∏ i ∈ R, g i) * (∏ i ∈ R, g i) * D ^ p ≤
    (∏ i ∈ R, x i) * (∏ i ∈ R, x i) * (∏ i ∈ R, x i) * A ^ p at h
  rw [hprod] at h
  let P := ∏ i ∈ R, x i
  have hpos : 0 < P := Finset.prod_pos (fun i _ => xpos i)
  change 2 ^ (3 * ∑ i ∈ R, e i) * D ^ p ≤ A ^ p
  apply Nat.le_of_mul_le_mul_right (c := P * P * P) _ (Nat.mul_pos (Nat.mul_pos hpos hpos) hpos)
  rw [show 3 * (∑ i ∈ R, e i) = (∑ i ∈ R, e i) + (∑ i ∈ R, e i) + (∑ i ∈ R, e i) by omega]
  simpa only [P, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
