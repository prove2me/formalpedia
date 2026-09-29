-- Prove2me | Theorems.Thm_AutomorphicForm_existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one
-- name    : AutomorphicForm.existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/3b132caf-3fa4-5c4d-b8a9-0b6a281cbb16
-- title:
--   Unique unipotent σ-twisted diagonalisation when N(a/b)≠ 1
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra that is finite dimensional over $F$, let $\sigma\colon L\simeq L$ be an $F$-algebra automorphism, and let $\gamma\in GL_2(L)$ be such that the underlying matrix has $(1,0)$ entry equal to $0$, i.e. $\gamma$ is upper triangular, with diagonal entries $a=\gamma_{00}$, $b=\gamma_{11}$ and upper entry $c=\gamma_{01}$. Assume further that the field norm $N_{L/F}(a/b)$, taken as `Algebra.norm F` of the quotient $\gamma_{00}/\gamma_{11}$, is not equal to $1$. Then there is exactly one $s\in L$ for which the $(0,1)$ entry of the matrix underlying [`AutomorphicForm.sigmaConj`](def/AutomorphicForm_SigmaConjugacy.html#L11) applied to $\sigma$ (viewed as a ring homomorphism), the unipotent element [`AutomorphicForm.unipotentGL2 s`](def/AutomorphicForm_ConstantTerm.html#L17) $=\begin{pmatrix}1&s\\0&1\end{pmatrix}$ and $\gamma$ vanishes; by the definition of [`AutomorphicForm.sigmaConj`](def/AutomorphicForm_SigmaConjugacy.html#L11) this element is $u(s)\,\gamma\,\bigl(\sigma(u(s))\bigr)^{-1}$, where $\sigma$ acts entrywise, so the assertion is that $c+sb-a\,\sigma(s)=0$ holds for a unique $s$. (The Lean conclusion asserts only the vanishing of that one entry, not explicitly that the resulting matrix is $\mathrm{diag}(a,b)$.)
--
--   This is the parametrisation of the upper triangular elements of $GL_2(L)$ whose diagonal ratio has norm different from $1$ by $\sigma$-twisted orbits of the upper unipotent subgroup: each such element is $\sigma$-conjugate to its diagonal part by a unique unipotent matrix, in the form of Langlands's lemmas on the hyperbolic terms in the twisted trace formula for $GL(2)$. It is used in the project's computation unfolding the constant term over these elements into an integral over the unipotent group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one.lean

import Definitions.Def_AutomorphicForm_SigmaConjugacy
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.existsUnique_sigmaConj_unipotentGL2_apply_zero_one_eq_zero_of_norm_div_ne_one
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (σ : L ≃ₐ[F] L) (γ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hN : Algebra.norm F ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    ∃! s : L, ((AutomorphicForm.sigmaConj (σ : L →+* L) (AutomorphicForm.unipotentGL2 s) γ :
        Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by sorry
