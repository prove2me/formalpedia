-- Prove2me | Theorems.Thm_BurauFaithful_modular_T_zpow_mul
-- name    : BurauFaithful.modular_T_zpow_mul
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T05:43:17.344988+00:00
-- url     : https://prove2.me/theorems/b6215062-321e-4eba-829c-12295e42e315
-- title:
--   The Euclidean step: right multiplication by $T^n$ adds $n$ times the first column to the second
-- statement:
--   The elementary step of the Euclidean algorithm for $\mathrm{SL}(2,\mathbb Z)$, phrased for the classical generator $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$: for every integral $2\times 2$ matrix $M$ and every $n\in\mathbb Z$, right multiplication by $T^n$ adds $n$ times the first column to the second column,
--   $$M\cdot T^{\,n}=\begin{pmatrix} M_{00} & M_{01}+n\,M_{00}\\ M_{10} & M_{11}+n\,M_{10}\end{pmatrix}.$$
--
--   This is the engine of the continued-fraction normal form $M=\pm S^{\varepsilon}T^{a_1}ST^{a_2}\cdots$ of an element of the modular group: it produces, for suitable $n$, a matrix whose $(0,0)$-entry is the remainder of $M_{00}$ modulo $M_{10}$, so that the absolute value of the bottom-left entry decreases.
--
--   **Formalization Note** The matrix power $T^n$ with integer exponent $n$ is expanded by `ModularGroup.coe_T_zpow`; the two sides are then compared entrywise.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, pp. 129-130 (the Euclidean algorithm in the modular group); C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups*, 2nd ed., Springer 1964, p. 85.

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem BurauFaithful.modular_T_zpow_mul (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℤ) :
    M * (↑(ModularGroup.T ^ n) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![M 0 0, M 0 1 + n * M 0 0; M 1 0, M 1 1 + n * M 1 0] := by sorry
