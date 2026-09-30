-- Prove2me | solution 1 for rota_basis_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:12.416816+00:00
-- url     : https://prove2.me/submissions/3b143255-6849-4c10-ac0f-19fe072d2bf3

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

private noncomputable def rows (i j : Fin 2) : Fin 2 → ℝ :=
  Pi.basisFun ℝ (Fin 2) (if i = 0 then j else Equiv.swap 0 1 j)

private theorem rows_independent : ∀ i : Fin 2, LinearIndependent ℝ (rows i) := by
  intro i
  fin_cases i
  · change LinearIndependent ℝ (fun j => Pi.basisFun ℝ (Fin 2) j)
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent
  · change LinearIndependent ℝ (fun j => Pi.basisFun ℝ (Fin 2) (Equiv.swap 0 1 j))
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent.comp
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap 0 1).injective

theorem solution : ¬ (∀ (n : ℕ), 1 ≤ n →
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V],
      Module.finrank ℝ V = n → ∀ (bases : Fin n → Fin n → V),
        (∀ i : Fin n, LinearIndependent ℝ (bases i)) →
        ∃ sigma : Fin n → Fin n, Function.Injective sigma ∧
          LinearIndependent ℝ (fun i => bases i (sigma i))) := by
  intro h
  obtain ⟨sigma, hinj, hind⟩ := h 2 (by decide) (Fin 2 → ℝ) (by simp) rows rows_independent
  have hne : sigma 0 ≠ sigma 1 := hinj.ne (by decide)
  have heq : rows 0 (sigma 0) = rows 1 (sigma 1) := by
    generalize hzero : sigma 0 = i at hne ⊢
    generalize hone : sigma 1 = j at hne ⊢
    fin_cases i <;> fin_cases j <;> simp [rows] at hne ⊢
  exact (by decide : (0 : Fin 2) ≠ 1) (hind.injective heq)
