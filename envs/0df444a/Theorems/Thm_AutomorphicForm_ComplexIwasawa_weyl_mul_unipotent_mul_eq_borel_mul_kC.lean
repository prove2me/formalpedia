-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC
-- name    : AutomorphicForm.ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/989187f3-ca6d-5005-87cb-3fbc8208da63
-- title:
--   Explicit Iwasawa factorisation of w n(z) g in GL₂(ℂ)
-- statement:
--   Let $g$ be a $2\times 2$ complex matrix with $\det g \neq 0$, and let $z \in \mathbb{C}$. Write $P = g_{00} + z\,g_{10}$ (`botP g z`), $Q = g_{01} + z\,g_{11}$ (`botQ g z`), and $r = \sqrt{|P|^2 + |Q|^2}$ (`radC g z`, defined as the real square root of $\mathrm{normSq}(P) + \mathrm{normSq}(Q)$), and let $kC\,g\,z$ be the matrix $\begin{pmatrix}\bar Q/r & -\bar P/r\\ P/r & Q/r\end{pmatrix}$, the divisions being by the real number $r$ coerced into $\mathbb{C}$. The assertion is the matrix identity $$\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&z\\0&1\end{pmatrix} g = \begin{pmatrix}-\det g / r & (g_{10}\bar P + g_{11}\bar Q)/r\\ 0 & r\end{pmatrix} \cdot kC\,g\,z,$$ an equality of $2\times 2$ complex matrices, in which the left factor on the right-hand side is upper triangular with diagonal entries $-\det g / r$ and $r$. The hypothesis $\det g \neq 0$ enters through the positivity of $r$, which makes the divisions by $r$ meaningful; it cannot be omitted, since for a singular $g$ one may have $P = Q = 0$, hence $r = 0$ and $kC\,g\,z = 0$.
--
--   This is the archimedean Iwasawa decomposition $GL_2(\mathbb{C}) = B(\mathbb{C})\cdot U(2)$ written out explicitly for the Weyl–unipotent translate $w\,n(z)\,g$, the Borel factor being recorded in terms of the bottom row of $w\,n(z)\,g$. It is used in the estimate [`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`](thm.html#AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary), where the unitary factor $kC\,g\,z$ is absorbed by a unitary representation and the remaining integral over $z$ is controlled by the triangular factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ComplexConjugate AutomorphicForm.ComplexIwasawa

theorem AutomorphicForm.ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![-g.det / (radC g z : ℂ),
            (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
           0, (radC g z : ℂ)] * kC g z := by sorry
