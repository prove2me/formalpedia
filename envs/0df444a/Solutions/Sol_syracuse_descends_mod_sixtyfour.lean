-- Prove2me | solution 1 for syracuse_descends_mod_sixtyfour
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-10T19:33:12.93998+00:00
-- url     : https://prove2.me/submissions/23f14ecf-2c06-44f3-8a7a-8fc3136c1086

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_uniform_descent

/-- One Syracuse step, certified by an explicit factorisation `3y+1 = 2^a z` with `z` odd. -/
theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


/-- Residue class `3 mod 64`: descends in 2 step(s), stripping [1, 4]. -/
theorem cls_3 (m : ℕ) (hodd : Odd m) (h : m % 64 = 3) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 3 = 5 := se 1 (by norm_num) (by decide)
  have s1 : syracuseStep 5 = 1 := se 4 (by norm_num) (by decide)
  refine ⟨2, syracuse_uniform_descent (fun i => if i = 0 then 1 else 4) m 3 6 2
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 3 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0, s1]
  · simp [Function.iterate_succ_apply', s0, s1]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `5 mod 64`: descends in 1 step(s), stripping [4]. -/
theorem cls_5 (m : ℕ) (hodd : Odd m) (h : m % 64 = 5) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 5 = 1 := se 4 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 4) m 5 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 5 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `9 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_9 (m : ℕ) (hodd : Odd m) (h : m % 64 = 9) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 9 = 7 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 9 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 9 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `13 mod 64`: descends in 1 step(s), stripping [3]. -/
theorem cls_13 (m : ℕ) (hodd : Odd m) (h : m % 64 = 13) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 13 = 5 := se 3 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 3) m 13 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 13 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `17 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_17 (m : ℕ) (hodd : Odd m) (h : m % 64 = 17) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 17 = 13 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 17 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 17 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `19 mod 64`: descends in 2 step(s), stripping [1, 3]. -/
theorem cls_19 (m : ℕ) (hodd : Odd m) (h : m % 64 = 19) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 19 = 29 := se 1 (by norm_num) (by decide)
  have s1 : syracuseStep 29 = 11 := se 3 (by norm_num) (by decide)
  refine ⟨2, syracuse_uniform_descent (fun i => if i = 0 then 1 else 3) m 19 6 2
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 19 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0, s1]
  · simp [Function.iterate_succ_apply', s0, s1]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `25 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_25 (m : ℕ) (hodd : Odd m) (h : m % 64 = 25) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 25 = 19 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 25 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 25 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `29 mod 64`: descends in 1 step(s), stripping [3]. -/
theorem cls_29 (m : ℕ) (hodd : Odd m) (h : m % 64 = 29) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 29 = 11 := se 3 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 3) m 29 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 29 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `33 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_33 (m : ℕ) (hodd : Odd m) (h : m % 64 = 33) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 33 = 25 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 33 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 33 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `37 mod 64`: descends in 1 step(s), stripping [4]. -/
theorem cls_37 (m : ℕ) (hodd : Odd m) (h : m % 64 = 37) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 37 = 7 := se 4 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 4) m 37 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 37 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `41 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_41 (m : ℕ) (hodd : Odd m) (h : m % 64 = 41) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 41 = 31 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 41 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 41 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `43 mod 64`: descends in 3 step(s), stripping [1, 2, 2]. -/
theorem cls_43 (m : ℕ) (hodd : Odd m) (h : m % 64 = 43) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 43 = 65 := se 1 (by norm_num) (by decide)
  have s1 : syracuseStep 65 = 49 := se 2 (by norm_num) (by decide)
  have s2 : syracuseStep 49 = 37 := se 2 (by norm_num) (by decide)
  refine ⟨3, syracuse_uniform_descent (fun i => if i = 0 then 1 else if i = 1 then 2 else 2) m 43 6 3
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 43 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0, s1, s2]
  · simp [Function.iterate_succ_apply', s0, s1, s2]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `45 mod 64`: descends in 1 step(s), stripping [3]. -/
theorem cls_45 (m : ℕ) (hodd : Odd m) (h : m % 64 = 45) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 45 = 17 := se 3 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 3) m 45 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 45 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `49 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_49 (m : ℕ) (hodd : Odd m) (h : m % 64 = 49) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 49 = 37 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 49 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 49 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `51 mod 64`: descends in 2 step(s), stripping [1, 3]. -/
theorem cls_51 (m : ℕ) (hodd : Odd m) (h : m % 64 = 51) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 51 = 77 := se 1 (by norm_num) (by decide)
  have s1 : syracuseStep 77 = 29 := se 3 (by norm_num) (by decide)
  refine ⟨2, syracuse_uniform_descent (fun i => if i = 0 then 1 else 3) m 51 6 2
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 51 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0, s1]
  · simp [Function.iterate_succ_apply', s0, s1]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `53 mod 64`: descends in 1 step(s), stripping [5]. -/
theorem cls_53 (m : ℕ) (hodd : Odd m) (h : m % 64 = 53) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 53 = 5 := se 5 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 5) m 53 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 53 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `55 mod 64`: descends in 3 step(s), stripping [1, 1, 3]. -/
theorem cls_55 (m : ℕ) (hodd : Odd m) (h : m % 64 = 55) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 55 = 83 := se 1 (by norm_num) (by decide)
  have s1 : syracuseStep 83 = 125 := se 1 (by norm_num) (by decide)
  have s2 : syracuseStep 125 = 47 := se 3 (by norm_num) (by decide)
  refine ⟨3, syracuse_uniform_descent (fun i => if i = 0 then 1 else if i = 1 then 1 else 3) m 55 6 3
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 55 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0, s1, s2]
  · simp [Function.iterate_succ_apply', s0, s1, s2]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `57 mod 64`: descends in 1 step(s), stripping [2]. -/
theorem cls_57 (m : ℕ) (hodd : Odd m) (h : m % 64 = 57) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 57 = 43 := se 2 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 2) m 57 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 57 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

/-- Residue class `61 mod 64`: descends in 1 step(s), stripping [3]. -/
theorem cls_61 (m : ℕ) (hodd : Odd m) (h : m % 64 = 61) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  have s0 : syracuseStep 61 = 23 := se 3 (by norm_num) (by decide)
  refine ⟨1, syracuse_uniform_descent (fun i => 3) m 61 6 1
    hodd (by decide) ?_ ?_ (by decide) (by decide) ?_ ?_⟩
  · show m % 2 ^ 6 = 61 % 2 ^ 6
    norm_num [h]
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply', s0]
  · simp [Function.iterate_succ_apply', s0]
  · have := Nat.mod_le m 64
    omega

theorem solution (m : ℕ) (hodd : Odd m)
    (h : m % 64 = 3 ∨
      m % 64 = 5 ∨
      m % 64 = 9 ∨
      m % 64 = 13 ∨
      m % 64 = 17 ∨
      m % 64 = 19 ∨
      m % 64 = 25 ∨
      m % 64 = 29 ∨
      m % 64 = 33 ∨
      m % 64 = 37 ∨
      m % 64 = 41 ∨
      m % 64 = 43 ∨
      m % 64 = 45 ∨
      m % 64 = 49 ∨
      m % 64 = 51 ∨
      m % 64 = 53 ∨
      m % 64 = 55 ∨
      m % 64 = 57 ∨
      m % 64 = 61) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact cls_3 m hodd h
  · exact cls_5 m hodd h
  · exact cls_9 m hodd h
  · exact cls_13 m hodd h
  · exact cls_17 m hodd h
  · exact cls_19 m hodd h
  · exact cls_25 m hodd h
  · exact cls_29 m hodd h
  · exact cls_33 m hodd h
  · exact cls_37 m hodd h
  · exact cls_41 m hodd h
  · exact cls_43 m hodd h
  · exact cls_45 m hodd h
  · exact cls_49 m hodd h
  · exact cls_51 m hodd h
  · exact cls_53 m hodd h
  · exact cls_55 m hodd h
  · exact cls_57 m hodd h
  · exact cls_61 m hodd h
