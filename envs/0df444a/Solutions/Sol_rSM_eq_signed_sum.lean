-- Prove2me | solution 1 for rSM_eq_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:40:27.730715+00:00
-- url     : https://prove2.me/submissions/2830e578-4874-4e7b-a3a9-04765435722a

import Mathlib

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace SignedCoordinateProof

abbrev RealMatrix (n1 n2 : Nat) := Matrix (Fin n1) (Fin n2) ℝ

def rademacherSign {n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2)) (i : Fin n1) (j : Fin n2) : Real :=
  if (i, j) ∈ eps then 1 else -1

noncomputable def rademacherSampledMatrix {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ * if (i, j) ∈ Omega then rademacherSign eps i j * X i j else 0

noncomputable def coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (c : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j => if (i, j) = c then p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0) else 0

end SignedCoordinateProof

open SignedCoordinateProof in
theorem solution {n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2))
    (p : Real) (X : RealMatrix n1 n2) :
    rademacherSampledMatrix Omega eps p X =
      ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • coordScaled Omega p X c := by
  ext i j
  simp [rademacherSampledMatrix, coordScaled, Matrix.sum_apply, Matrix.smul_apply,
    mul_ite, mul_assoc, mul_left_comm, mul_comm]
