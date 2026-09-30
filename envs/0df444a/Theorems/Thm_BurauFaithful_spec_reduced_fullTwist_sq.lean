-- Prove2me | Theorems.Thm_BurauFaithful_spec_reduced_fullTwist_sq
-- name    : BurauFaithful.spec_reduced_fullTwist_sq
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T04:54:45.797558+00:00
-- url     : https://prove2.me/theorems/2e11b265-2121-4eca-8a0a-b7b7050bee79
-- title:
--   The full twist maps to $-I$ in the specialized reduced Burau representation at $t=-1$
-- statement:
--   The specialization at $t=-1$ of the 2-dimensional reduced Burau representation sends the full twist $\Delta^2 = (\sigma_1\sigma_2)^3$ to the central element $-1$ of $\mathrm{SL}(2,\mathbb Z)$.
--
--   With $A=\begin{pmatrix}1&-1\\0&1\end{pmatrix}$ and $B=\begin{pmatrix}2&-1\\1&0\end{pmatrix}$ the images of the two generators, the statement is
--
--   $$(AB)^3 = -I \in \mathrm{SL}(2,\mathbb Z).$$
--
--   Since $-1$ is the non-trivial central element of $\mathrm{SL}(2,\mathbb Z)$ (of order $2$), this says that the image of $\Delta^2$ has order exactly $2$, while the separate statement `BurauFaithful.spec_reduced_coxeter` records $(AB)^6=1$, i.e. the image of $\Delta^4=(\sigma_1\sigma_2)^6$ is trivial. Hence the kernel of the specialization contains $\Delta^4$ but not $\Delta^2$, which together with the Coxeter-Moser presentation pins the kernel down to $\langle\Delta^4\rangle$ (Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, §3.3, pp. 129-130).
--
--   **Formalization Note** The elements are written as subtype elements of `Matrix.SpecialLinearGroup (Fin 2) ℤ` with matrix literals; the equality is a finite computation over the integers.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, Theorem 3.15, pp. 129-130 (the image of the full twist in the modular group); C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups*, 2nd ed., Springer 1964, p. 85.

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem BurauFaithful.spec_reduced_fullTwist_sq :
    ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0]) ^ 3 =
      (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by sorry
