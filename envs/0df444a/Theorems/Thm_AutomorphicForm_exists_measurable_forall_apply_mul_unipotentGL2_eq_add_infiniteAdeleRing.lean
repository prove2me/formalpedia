-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing
-- name    : AutomorphicForm.exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/8e425872-8343-519e-a0d4-9da50bdf6af3
-- title:
--   A Borel unipotent coordinate on M₂(K_∞)
-- statement:
--   Let $K$ be a number field and let $K_\infty$ denote its infinite adele ring $\prod_{v\mid\infty}K_v$. The assertion is the existence of a map $y$ from the full matrix algebra $M_2(K_\infty)$ to the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ attached to $K$ with the following two properties. First, $y$ is measurable when $M_2(K_\infty)$ carries the Borel $\sigma$-algebra of its topology (the $\sigma$-algebra `borel _`, imposed explicitly rather than taken from an ambient instance) and the mixed space carries its own measurable structure. Second, $y$ is additive along right translation by upper unipotent matrices on the invertible locus: for every unit $g \in \mathrm{GL}_2(K_\infty)$ and every $x \in K_\infty$, the value of $y$ on the matrix underlying the product $g \cdot \mathtt{unipotentGL2}\,x$, where $\mathtt{unipotentGL2}\,x$ is the invertible matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$, equals $y$ of the matrix underlying $g$ plus the image of $x$ under the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K` from $K_\infty$ onto $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$. No condition is imposed on the values of $y$ on singular matrices.
--
--   The map $y$ is a Borel coordinate along the fibres of the right action of the unipotent subgroup $N=\{\begin{pmatrix}1&x\\0&1\end{pmatrix}\}$ on $\mathrm{GL}_2(K_\infty)$, identifying each coset $gN$ with $K_\infty \cong \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ in a Borel-measurable way. It serves to produce test functions on $\mathrm{GL}_2$ of the adeles with prescribed integral along every unipotent fibre, and is used in the evaluation of the constant in the Weil integration formula $\int_G = \int_{G/N}\int_N$ for $\mathrm{GL}_2$ that expresses a global integral in terms of the Dedekind zeta function at $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.lean

import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem AutomorphicForm.exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K] :
    ∃ y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) → mixedEmbedding.mixedSpace K,
      Measurable[borel _] y ∧
      ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (x : InfiniteAdeleRing K),
        y ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
          y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) + InfiniteAdeleRing.ringEquiv_mixedSpace K x := by sorry
