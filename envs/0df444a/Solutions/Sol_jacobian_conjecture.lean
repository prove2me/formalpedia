-- Prove2me | solution 1 for jacobian_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @evgeth
-- created : 2026-09-07T15:32:25.858469+00:00
-- url     : https://prove2.me/submissions/009b32bc-b62d-4552-b76a-cedd930fa0e3

import Mathlib

open MvPolynomial

noncomputable section

namespace JacobianCounterexample

abbrev R := MvPolynomial (Fin 3) ℂ

def x : R := X 0
def y : R := X 1
def z : R := X 2
def c (q : ℂ) : R := C q

theorem c_nat (n : ℕ) : c (n : ℂ) = (n : R) := by
  simpa [c] using (C_eq_coe_nat (σ := Fin 3) (R := ℂ) n)

theorem c_1 : c 1 = (1 : R) := by
  rw [show (1 : ℂ) = ((1 : ℕ) : ℂ) by norm_num, c_nat]; norm_num
theorem c_2 : c 2 = (2 : R) := by
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, c_nat]; norm_num
theorem c_3 : c 3 = (3 : R) := by
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, c_nat]; norm_num
theorem c_4 : c 4 = (4 : R) := by
  rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, c_nat]; norm_num
theorem c_6 : c 6 = (6 : R) := by
  rw [show (6 : ℂ) = ((6 : ℕ) : ℂ) by norm_num, c_nat]; norm_num
theorem c_7 : c 7 = (7 : R) := by
  rw [show (7 : ℂ) = ((7 : ℕ) : ℂ) by norm_num, c_nat]; norm_num
theorem c_9 : c 9 = (9 : R) := by
  rw [show (9 : ℂ) = ((9 : ℕ) : ℂ) by norm_num, c_nat]; norm_num

@[simp]
theorem pderiv_c (i : Fin 3) (q : ℂ) : pderiv i (c q) = 0 := by
  simp [c]

/-- The three components of the map. -/
def f₀ : R :=
  (c 1 + x * y) ^ 3 * z + y ^ 2 * (c 1 + x * y) * (c 4 + c 3 * x * y)

def f₁ : R :=
  y + c 3 * x * (c 1 + x * y) ^ 2 * z + c 3 * x * y ^ 2 * (c 4 + c 3 * x * y)

def f₂ : R :=
  c 2 * x - c 3 * x ^ 2 * y - x ^ 3 * z

def F : Fin 3 → R := ![f₀, f₁, f₂]

/-- Two distinct points with the same image. -/
def a : Fin 3 → ℂ := ![0, 0, -1 / 4]
def b : Fin 3 → ℂ := ![1, -3 / 2, 13 / 2]

theorem dx_f₀ : pderiv (0 : Fin 3) f₀ =
    c 3 * y * (c 1 + x * y) ^ 2 * z + y ^ 3 * (c 7 + c 6 * x * y) := by
  simp [f₀, x, y, z]
  rw [c_1, c_3, c_4, c_6, c_7]
  ring

theorem dy_f₀ : pderiv (1 : Fin 3) f₀ =
    c 3 * x * (c 1 + x * y) ^ 2 * z +
      c 2 * y * (c 1 + x * y) * (c 4 + c 3 * x * y) +
      x * y ^ 2 * (c 7 + c 6 * x * y) := by
  simp [f₀, x, y, z]
  rw [c_1, c_2, c_3, c_4, c_6, c_7]
  ring

theorem dz_f₀ : pderiv (2 : Fin 3) f₀ = (c 1 + x * y) ^ 3 := by
  simp [f₀, x, y, z]

theorem dx_f₁ : pderiv (0 : Fin 3) f₁ =
    c 3 * (c 1 + x * y) ^ 2 * z + c 6 * x * y * (c 1 + x * y) * z +
      c 3 * y ^ 2 * (c 4 + c 3 * x * y) + c 9 * x * y ^ 3 := by
  simp [f₁, x, y, z]
  rw [c_1, c_3, c_4, c_6, c_9]
  ring

theorem dy_f₁ : pderiv (1 : Fin 3) f₁ =
    c 1 + c 6 * x ^ 2 * (c 1 + x * y) * z +
      c 6 * x * y * (c 4 + c 3 * x * y) + c 9 * x ^ 2 * y ^ 2 := by
  simp [f₁, x, y, z]
  rw [c_1, c_3, c_4, c_6, c_9]
  ring

theorem dz_f₁ : pderiv (2 : Fin 3) f₁ = c 3 * x * (c 1 + x * y) ^ 2 := by
  simp [f₁, x, y, z]

theorem dx_f₂ : pderiv (0 : Fin 3) f₂ = c 2 - c 6 * x * y - c 3 * x ^ 2 * z := by
  simp [f₂, x, y, z]
  rw [c_2, c_3, c_6]
  ring

theorem dy_f₂ : pderiv (1 : Fin 3) f₂ = -c 3 * x ^ 2 := by
  simp [f₂, x, y, z]

theorem dz_f₂ : pderiv (2 : Fin 3) f₂ = -x ^ 3 := by
  simp [f₂, x, y, z]

/-- The Jacobian determinant (rows indexed by the variable, columns by the component). -/
theorem jacobian_det_col :
    (Matrix.of (fun i j => pderiv i (F j))).det = C (-2 : ℂ) := by
  rw [Matrix.det_fin_three]
  change
    pderiv 0 f₀ * pderiv 1 f₁ * pderiv 2 f₂ -
      pderiv 0 f₀ * pderiv 1 f₂ * pderiv 2 f₁ -
      pderiv 0 f₁ * pderiv 1 f₀ * pderiv 2 f₂ +
      pderiv 0 f₁ * pderiv 1 f₂ * pderiv 2 f₀ +
      pderiv 0 f₂ * pderiv 1 f₀ * pderiv 2 f₁ -
      pderiv 0 f₂ * pderiv 1 f₁ * pderiv 2 f₀ = C (-2 : ℂ)
  rw [dx_f₀, dy_f₀, dz_f₀, dx_f₁, dy_f₁, dz_f₁, dx_f₂, dy_f₂, dz_f₂]
  rw [c_1, c_2, c_3, c_4, c_6, c_7, c_9]
  rw [show C (-2 : ℂ) = (-2 : R) by
    calc
      C (-2 : ℂ) = -C (2 : ℂ) := by
        rw [show (-2 : ℂ) = -(2 : ℂ) by norm_num, map_neg]
      _ = -(2 : R) := congrArg Neg.neg (C_eq_coe_nat (σ := Fin 3) (R := ℂ) 2)
      _ = (-2 : R) := rfl]
  ring

/-- The Jacobian determinant in the row convention of the target statement. -/
theorem jacobian_det :
    (Matrix.of (fun i j => pderiv j (F i))).det = C (-2 : ℂ) := by
  have h : (Matrix.of (fun i j => pderiv j (F i)))
      = Matrix.transpose (Matrix.of (fun i j => pderiv i (F j))) := by
    ext i j
    rfl
  rw [h, Matrix.det_transpose, jacobian_det_col]

theorem same_fiber :
    (fun i => eval a (F i)) = (fun i => eval b (F i)) := by
  funext i
  fin_cases i <;> simp [F, f₀, f₁, f₂, x, y, z, c, a, b] <;> norm_num

end JacobianCounterexample

theorem solution :
    ¬ (∀ (n : ℕ) (hn : 0 < n) (F : Fin n → MvPolynomial (Fin n) ℂ)
        (hJ : ∃ c : ℂ, c ≠ 0 ∧
          Matrix.det (Matrix.of (fun i j => MvPolynomial.pderiv j (F i))) =
            MvPolynomial.C c),
        Function.Bijective (fun x : Fin n → ℂ => fun i => MvPolynomial.eval x (F i))) := by
  intro h
  have hJ : ∃ c : ℂ, c ≠ 0 ∧
      Matrix.det (Matrix.of (fun i j => MvPolynomial.pderiv j (JacobianCounterexample.F i))) =
        MvPolynomial.C c :=
    ⟨-2, by norm_num, JacobianCounterexample.jacobian_det⟩
  have hbij := h 3 (by norm_num) JacobianCounterexample.F hJ
  have hab := hbij.1 JacobianCounterexample.same_fiber
  have h0 := congrFun hab 0
  norm_num [JacobianCounterexample.a, JacobianCounterexample.b] at h0
