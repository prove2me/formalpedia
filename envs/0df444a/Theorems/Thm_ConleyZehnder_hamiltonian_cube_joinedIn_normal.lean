-- Prove2me | Theorems.Thm_ConleyZehnder_hamiltonian_cube_joinedIn_normal
-- name    : ConleyZehnder.hamiltonian_cube_joinedIn_normal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:20:37.748768+00:00
-- url     : https://prove2.me/theorems/232d31ff-190b-40cc-bdcd-e390c2bdf84e
-- title:
--   A Hamiltonian matrix $Y$ with $Y^3=9Y$ is joined, avoiding eigenvalue $1$, to $0$ or to $\mathrm{diag}(3,0,\dots,0,-3,0,\dots,0)$
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\ \mathrm{Id}&0\end{pmatrix}$ and call a real $2n\times 2n$ matrix $X$ *Hamiltonian* if $XJ_0+J_0X^{T}=0$. Let $\mathcal H^*(2n)$ be the set of Hamiltonian matrices $X$ such that $1$ is not an eigenvalue of $X$, i.e. $\det(\mathrm{Id}-X)\neq 0$, with the topology of $\mathbb R^{2n\times 2n}$.
--
--   Let $Y$ be a Hamiltonian matrix with $Y^3=9Y$. Then there is a continuous path $[0,1]\to\mathcal H^*(2n)$ from $Y$ to $0$ or to $Y_-=\mathrm{diag}(3,0,\dots,0,-3,0,\dots,0)$, the diagonal matrix with entry $3$ at the first coordinate of the first block, $-3$ at the first coordinate of the second block, and $0$ elsewhere.
--
--   Together with its companion statement, this shows that every element of $\mathcal H^*(2n)$ lies in the path component of $0$ or of $\mathrm{diag}(3,0,\dots,0,-3,0,\dots,0)$ in $\mathcal H^*(2n)$. It serves the description of the path components of $\mathrm{Sp}^*(2n)$ used in the definition of the Conley–Zehnder index.
--
--   Formalization note: `Mat n` is the type of real matrices indexed by `Fin n ⊕ Fin n` and `J₀ n` is Mathlib's `Matrix.J`, both from the definition module `ConleyZehnder_Setting`; the set $\mathcal H^*(2n)$ is written inline, and "joined by a continuous path inside a set" is Mathlib's `JoinedIn`. For $n=0$ the statement is trivial.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, the first of the two facts listed before Definition 7, p. 6 (every element of Sp*(2n) is joined inside Sp*(2n) to W+ or W-); this statement is an intermediate step towards that fact, formulated for Hamiltonian matrices, and is not stated in this form in the reference

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

open Matrix

/-- A real Hamiltonian matrix `Y` (`Y J₀ + J₀ Yᵀ = 0`) with `Y³ = 9 Y` is joined, inside the set of
Hamiltonian matrices without eigenvalue `1`, to `0` or to `diag(3, 0, …, 0, -3, 0, …, 0)`. -/
theorem hamiltonian_cube_joinedIn_normal {n : ℕ} (Y : Mat n) (hY : Y * J₀ n + J₀ n * Yᵀ = 0)
    (h3 : Y * Y * Y = (9 : ℝ) • Y) :
    JoinedIn {Z : Mat n | Z * J₀ n + J₀ n * Zᵀ = 0 ∧ (1 - Z).det ≠ 0} Y 0 ∨
      JoinedIn {Z : Mat n | Z * J₀ n + J₀ n * Zᵀ = 0 ∧ (1 - Z).det ≠ 0} Y
        (Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (3 : ℝ) else 0)
          (fun j : Fin n => if j.val = 0 then (-3 : ℝ) else 0))) := by sorry

end ConleyZehnder
