-- Prove2me | Theorems.Thm_ConleyZehnder_symplectic_cayley_isHermitian
-- name    : ConleyZehnder.symplectic_cayley_isHermitian
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T23:25:28.632641+00:00
-- url     : https://prove2.me/theorems/5853d951-74e0-496c-ba5c-a07f6bda5d16
-- title:
--   Symmetry of the matrix J₀(A − Id)(A + Id)⁻¹ for symplectic A
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ and let $A$ be a real $2n\times 2n$ symplectic matrix, $AJ_0A^{T}=J_0$, such that $-1$ is not an eigenvalue of $A$. Then the matrix
--   $$N=J_0\,(A-\mathrm{Id})\,(A+\mathrm{Id})^{-1}$$
--   is symmetric: $N^{T}=N$.
--
--   This is the symmetric matrix whose signature computes the Conley–Zehnder index of paths that avoid the eigenvalue $-1$ (`czIndex_two_mul_eq_neg_signature`). The statement supplies the symmetry hypothesis needed to apply that formula and `signature_eq_zero_of_hyperbolic`.
--
--   Formalization note: `J₀`, `IsSymplectic` and `Mat n` come from the definition module `ConleyZehnder_Setting`. Symmetry is Mathlib's `Matrix.IsHermitian` over `ℝ`, which for real matrices is $N^{T}=N$. "No eigenvalue $-1$" is `(A + 1).det ≠ 0`.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239); Cayley transform of symplectic matrices (standard)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- If `A` is symplectic and `-1` is not an eigenvalue of `A`, then `J₀ (A - Id) (A + Id)⁻¹` is
symmetric. -/
theorem symplectic_cayley_isHermitian {n : ℕ} (A : Mat n) (hA : IsSymplectic A)
    (hd : (A + 1).det ≠ 0) :
    (J₀ n * (A - 1) * (A + 1)⁻¹).IsHermitian := by sorry

end ConleyZehnder
