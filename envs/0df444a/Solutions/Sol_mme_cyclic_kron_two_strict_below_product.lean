-- Prove2me | solution 1 for mme_cyclic_kron_two_strict_below_product
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T12:15:45.850645+00:00
-- url     : https://prove2.me/submissions/52dfdc58-7ca6-495f-9b92-7476fec04421

import Mathlib.Tactic
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

set_option autoImplicit false

/-- The ordered two-factor Kronecker product `kronFin 2 [A^1, B^1]` is isomorphic to
`A ⊗ B`: pass to the tensor quotient, where `kronFin` becomes a finite product and
first powers reduce to the factors. -/
theorem kronFin_two_first_powers_iso.{u} {K : Type u} [Field K] (A B : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 2 (fun i => ((![A, B] : Fin 2 → TensorObj K 3) i).kronPow
        ((![1, 1] : Fin 2 → ℕ) i)))
      (TensorObj.kron A B) := by
  rw [← TensorQ.toQ_eq_iff, mme_toQ_kronFin, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [TensorObj.kronPow, ← TensorQ.toQ_mul, ← TensorQ.toQ_one, mul_one]

theorem solution.{u}
    {K : Type u} [Field K]
    (A B : TensorObj K 3) (tau endpointA endpointB : ℝ)
    (hendpointA : 0 < endpointA) (hendpointB : 0 < endpointB)
    (hA : ∀ V : ℝ, 0 ≤ V → V < endpointA →
      HasTauValueAtLeast (cyclicSymmetrization A) tau V)
    (hB : ∀ V : ℝ, 0 ≤ V → V < endpointB →
      HasTauValueAtLeast (cyclicSymmetrization B) tau V)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < endpointA * endpointB) :
    HasTauValueAtLeast
      (cyclicSymmetrization (TensorObj.kron A B)) tau V := by
  have hprod := mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    (K := K) (n := 2) ![A, B] ![1, 1] tau ![endpointA, endpointB]
    (by
      intro i
      fin_cases i
      · simpa using hendpointA
      · simpa using hendpointB)
    (by
      intro i
      fin_cases i
      · simpa using hA
      · simpa using hB)
    V hV (by simpa [Fin.prod_univ_two] using hVlt)
  exact mme_HasTauValueAtLeast_mono_restrict
    (mme_cyclicSymmetrization_mono_restrict (kronFin_two_first_powers_iso A B).1) hprod
