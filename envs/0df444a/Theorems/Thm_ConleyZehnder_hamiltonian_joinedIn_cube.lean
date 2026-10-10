-- Prove2me | Theorems.Thm_ConleyZehnder_hamiltonian_joinedIn_cube
-- name    : ConleyZehnder.hamiltonian_joinedIn_cube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:20:47.340814+00:00
-- url     : https://prove2.me/theorems/925da181-6b24-4428-a9c6-ab2913b0be8f
-- title:
--   Every Hamiltonian matrix without eigenvalue $1$ is joined, avoiding eigenvalue $1$, to a Hamiltonian $Y$ with $Y^3=9Y$
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\ \mathrm{Id}&0\end{pmatrix}$ and call a real $2n\times 2n$ matrix $X$ *Hamiltonian* if $XJ_0+J_0X^{T}=0$. Let $\mathcal H^*(2n)$ be the set of Hamiltonian matrices $X$ such that $1$ is not an eigenvalue of $X$, i.e. $\det(\mathrm{Id}-X)\neq 0$, with the topology of $\mathbb R^{2n\times 2n}$.
--
--   For every $X\in\mathcal H^*(2n)$ there exist a Hamiltonian matrix $Y$ with $Y^3=9Y$ and a continuous path $[0,1]\to\mathcal H^*(2n)$ from $X$ to $Y$. (Such a $Y$ automatically lies in $\mathcal H^*(2n)$.)
--
--   Together with its companion statement, this shows that every element of $\mathcal H^*(2n)$ lies in the path component of $0$ or of $\mathrm{diag}(3,0,\dots,0,-3,0,\dots,0)$ in $\mathcal H^*(2n)$. It serves the description of the path components of $\mathrm{Sp}^*(2n)$ used in the definition of the Conley–Zehnder index.
--
--   Formalization note: `Mat n` is the type of real matrices indexed by `Fin n ⊕ Fin n` and `J₀ n` is Mathlib's `Matrix.J`, both from the definition module `ConleyZehnder_Setting`; the set $\mathcal H^*(2n)$ is written inline, and "joined by a continuous path inside a set" is Mathlib's `JoinedIn`. For $n=0$ the statement is trivial.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, the first of the two facts listed before Definition 7, p. 6 (every element of Sp*(2n) is joined inside Sp*(2n) to W+ or W-); this statement is an intermediate step towards that fact, formulated for Hamiltonian matrices, and is not stated in this form in the reference

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

open Matrix

/-- Every real Hamiltonian matrix `X` (`X J₀ + J₀ Xᵀ = 0`) without eigenvalue `1` is joined, inside
the set of Hamiltonian matrices without eigenvalue `1`, to a Hamiltonian matrix `Y` with
`Y³ = 9 Y`. -/
theorem hamiltonian_joinedIn_cube {n : ℕ} (X : Mat n) (hX : X * J₀ n + J₀ n * Xᵀ = 0)
    (h1 : (1 - X).det ≠ 0) :
    ∃ Y : Mat n, Y * J₀ n + J₀ n * Yᵀ = 0 ∧ Y * Y * Y = (9 : ℝ) • Y ∧
      JoinedIn {Z : Mat n | Z * J₀ n + J₀ n * Zᵀ = 0 ∧ (1 - Z).det ≠ 0} X Y := by sorry

end ConleyZehnder
