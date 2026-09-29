-- Prove2me | Theorems.Thm_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one
-- name    : AutomorphicForm.exists_uniform_iwasawa_mul_of_glFin_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/301adb92-c4fe-5922-aef7-18c81b7df2dc
-- title:
--   Uniform Iwasawa coordinates for isometric translates of g
-- statement:
--   Let $K$ be a number field, and let $g$ be an element of $\mathrm{GL}_2$ of the adele ring of $K$ whose finite part is the identity, i.e. the entrywise image of $g$ under the projection to $\mathrm{GL}_2$ of the finite adele ring (`glFin`) is $1$. The assertion is the existence of real constants $m, M$ with $0 < m \le M$, depending only on $g$, such that the following holds for every $k \in \mathrm{GL}_2$ of the adele ring whose finite part is the identity and whose archimedean component at each infinite place $w$ (the image of $k$ in $\mathrm{GL}_2(K_w)$ under the adelic-to-infinite and then place-$w$ evaluation maps) satisfies `IsRowIsometry`, that is, has determinant of norm $1$ and satisfies $\|x a_{00} + y a_{10}\|^2 + \|x a_{01} + y a_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x, y \in K_w$, where $a$ is its matrix: there are an adele $\nu$ with zero finite part, ideles $z, b$ with finite part $1$, and a $k'$ subject to the same two conditions as $k$ (identity finite part, row-isometric archimedean components at all infinite places), such that $$k\,g = \begin{pmatrix}1&\nu\\0&1\end{pmatrix}\begin{pmatrix}z&0\\0&z\end{pmatrix}\begin{pmatrix}b&0\\0&1\end{pmatrix} k',$$ and such that at every infinite place $w$ the archimedean components satisfy $m \le \|z_w\| \le M$ and $m \le \|b_w\| \le M$.
--
--   This is the archimedean Iwasawa decomposition $G = N Z A K_\infty$ for $\mathrm{GL}_2$ over the adeles, in the uniform form asserting that as $k$ ranges over the row-isometric group with trivial finite part, the torus coordinates of $kg$ stay in a fixed compact range determined by $g$. It is used to bound Whittaker coefficients of translates, in [`AutomorphicForm.norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one`](thm.html#AutomorphicForm.norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one), and rests on the adelic Borel-times-isometry factorisation [`AutomorphicForm.exists_mem_adelicBorel_mul_eq`](thm.html#AutomorphicForm.exists_mem_adelicBorel_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_uniform_iwasawa_mul_of_glFin_eq_one
    (K : Type) [Field K] [NumberField K]
    (g : AdelicGL2 (𝓞 K) K) (hg : glFin (𝓞 K) K g = 1) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (ν : AdeleRing (𝓞 K) K) (z b : (AdeleRing (𝓞 K) K)ˣ) (k' : AdelicGL2 (𝓞 K) K),
          ν.2 = 0 ∧ ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ((b : AdeleRing (𝓞 K) K)).2 = 1 ∧
          glFin (𝓞 K) K k' = 1 ∧
          (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k'))) ∧
          k * g = unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b * k' ∧
          (∀ w : InfinitePlace K, m ≤ ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ∧ ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ≤ M ∧
            m ≤ ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ∧ ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ≤ M) := by sorry
