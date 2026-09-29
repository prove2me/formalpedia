-- Prove2me | Theorems.Thm_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
-- name    : AutomorphicForm.exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e53ff582-26df-5a6c-bb4a-e935da3d3ec7
-- title:
--   Sign–central–determinant-one factorisation in the adelic maximal compact
-- statement:
--   Let $F$ be a number field and let $k$ be an element of $GL_2(\mathbb{A}_F)$ lying in [`AutomorphicForm.adelicMaximalCompact F`](def/AutomorphicForm_AdelicMaximalCompact.html#L19), that is: the finite-adelic component $\mathrm{glFin}(k)$ lies in the subgroup `finiteIntegralGL2` of integral matrices of level $\top$, and for every infinite place $w$ of $F$ the image $\mathrm{archComponent}\,w$ of the archimedean part of $k$ is a row isometry in the sense of `IsRowIsometry`: its determinant has absolute value $1$ and $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all $x,y$ in the completion $F_w$. Then there are ideles $a,z\in\mathbb{A}_F^\times$ and an element $k_1$ of $GL_2(\mathbb{A}_F)$ such that: the finite part of $a$ is $1$ and every archimedean component $a_w$ equals $1$ or $-1$; the central scalar matrix $\mathrm{diag}(z,z)$ lies in [`AutomorphicForm.adelicMaximalCompact F`](def/AutomorphicForm_AdelicMaximalCompact.html#L19); $k_1$ lies in [`AutomorphicForm.adelicMaximalCompact F`](def/AutomorphicForm_AdelicMaximalCompact.html#L19); for every infinite place $w$ the matrix $\mathrm{archComponent}\,w$ of the archimedean part of $k_1$ has determinant exactly $1$; and $k=\mathrm{diagOne}(a)\cdot\mathrm{diag}(z,z)\cdot k_1$, where $\mathrm{diagOne}(a)=\mathrm{diag}(a,1)$.
--
--   This is the adelic form of the place-by-place decompositions $O(2)=\{\pm1\}\ltimes SO(2)$ and $U(2)=U(1)\cdot SU(2)$, extracting from an element of the standard maximal compact subgroup a sign idele, a central unit idele and a factor whose archimedean determinants are trivial. It is used in the analysis of Eisenstein and Whittaker sections at maximal-compact level, where the central factor acts through the central character and the sign factor ranges over a set of $2^{\#\{w\mid\infty\}}$ elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F]
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ AutomorphicForm.adelicMaximalCompact F) :
    ∃ (a z : (AdeleRing (𝓞 F) F)ˣ) (k₁ : AdelicGL2 (𝓞 F) F),
      ((a : AdeleRing (𝓞 F) F).2 = 1 ∧
        ∀ w : InfinitePlace F, (a : AdeleRing (𝓞 F) F).1 w = 1 ∨ (a : AdeleRing (𝓞 F) F).1 w = -1) ∧
      AutomorphicForm.centralScalar (𝓞 F) F z ∈ AutomorphicForm.adelicMaximalCompact F ∧
      k₁ ∈ AutomorphicForm.adelicMaximalCompact F ∧
      (∀ w : InfinitePlace F,
        ((archComponent F w (glArch (𝓞 F) F k₁) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) ∧
      k = NumberField.AdelicLevel.diagOne a * AutomorphicForm.centralScalar (𝓞 F) F z * k₁ := by sorry
