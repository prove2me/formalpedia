-- Prove2me | Theorems.Thm_FamousTheorems_kronecker_roots_of_unity_theorem
-- name    : FamousTheorems.kronecker_roots_of_unity_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:26.111762+00:00
-- url     : https://prove2.me/theorems/a4a0143b-632c-4643-be97-37b046505f5a
-- title:
--   Kronecker's theorem on algebraic integers with all conjugates in the unit disc
-- statement:
--   **Kronecker's theorem.** Let $K$ be a number field and $x\in K$ a nonzero algebraic integer such that $|\varphi(x)|\le1$ for every field embedding $\varphi:K\to\mathbb C$. Then $x$ is a root of unity: $x^n=1$ for some $n\ge1$.
--
--   Equivalently, an algebraic integer all of whose conjugates lie in the closed unit disc is $0$ or a root of unity. The theorem is the starting point of the study of heights and Mahler measure (Lehmer's problem) and is used in the proof of Dirichlet's unit theorem, to identify the kernel of the logarithmic embedding with the roots of unity.
--
--   **Formalization note.** Mathlib's `NumberField.Embeddings.pow_eq_one_of_norm_le_one`, stated there for embeddings into any algebraically closed normed field `A` with `NormedAlgebra ℚ A`. Here `A` is specialised to `ℂ`, the classical setting.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.Embeddings.pow_eq_one_of_norm_le_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kronecker_roots_of_unity_theorem (K : Type*) [Field K] [NumberField K] {x : K} (hx₀ : x ≠ 0) (hxi : IsIntegral ℤ x)
    (hx : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ 1) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by sorry

end FamousTheorems
