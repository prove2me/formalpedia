-- Prove2me | Theorems.Thm_BurauFaithful_sl2_euclid_step
-- name    : BurauFaithful.sl2_euclid_step
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T05:55:56.819007+00:00
-- url     : https://prove2.me/theorems/67a39e8f-72ec-46fb-ad31-83fc574bedf7
-- title:
--   The Euclidean descent step in $\mathrm{SL}(2,\mathbb Z)$: $|(M T^n S)_{00}|<|M_{00}|$
-- statement:
--   The Euclidean descent in the modular group: one step of the continued fraction algorithm decreases the size of the top-left entry.
--
--   Let $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ be the standard generators of $\mathrm{SL}(2,\mathbb Z)$, and let $M$ be an integral $2\times2$ matrix whose $(0,0)$-entry is nonzero. Put $n=-\lfloor M_{01}/M_{00}\rfloor$ and
--   $$N=\bigl(M\cdot T^{\,n}\bigr)\cdot S .$$
--   Then the $(0,0)$-entry of $N$ is the remainder of $M_{01}$ modulo $M_{00}$,
--   $$N_{00}=M_{01}\bmod M_{00},\qquad\text{and}\qquad |N_{00}|<|M_{00}| .$$
--
--   Thus each step of the Euclidean algorithm replaces $M$ by a matrix whose top-left entry has strictly smaller absolute value; iterating and terminating when that entry vanishes produces the continued fraction normal form $M=\pm S^{\varepsilon}T^{a_1}ST^{a_2}\cdots$ of an element of the modular group (Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, §3.3, pp. 129–130).
--
--   **Formalization Note** The step combines `BurauFaithful.modular_T_zpow_mul` (right multiplication by $T^n$ adds $n$ times the first column to the second) with the column swap $S$; the arithmetic input is `Int.emod_lt_abs` together with `Int.emod_nonneg`.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, pp. 129-130; C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups*, 2nd ed., Springer 1964, p. 85.

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem BurauFaithful.sl2_euclid_step (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M 0 0 ≠ 0) :
    ((M * (↑(ModularGroup.T ^ (-(M 0 1 / M 0 0))) : Matrix (Fin 2) (Fin 2) ℤ)) *
        (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = M 0 1 % M 0 0 ∧
      |((M * (↑(ModularGroup.T ^ (-(M 0 1 / M 0 0))) : Matrix (Fin 2) (Fin 2) ℤ)) *
        (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)) 0 0| < |M 0 0| := by sorry
