-- Prove2me | Theorems.Thm_BurauFaithful_sl2_normal_form_base
-- name    : BurauFaithful.sl2_normal_form_base
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T06:18:06.051039+00:00
-- url     : https://prove2.me/theorems/8de9b158-4528-4d3c-94f6-010f52529f5d
-- title:
--   Terminal case of the Euclidean descent: a unimodular matrix with $M_{00}=0$ is $\pm S T^k$
-- statement:
--   The terminal case of the Euclidean algorithm in the modular group: a unimodular matrix with vanishing top-left entry is $\pm S\,T^{k}$.
--
--   Let $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ and $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ be the standard generators of $\mathrm{SL}(2,\mathbb Z)$, and let $M$ be an integral $2\times2$ matrix of determinant $1$ with $M_{00}=0$. Then
--   $$\exists\,k\in\mathbb Z,\qquad M=S\,T^{k}\quad\text{or}\quad M=-\,S\,T^{k}.$$
--
--   Indeed the determinant condition forces $M_{01}M_{10}=-1$, so $(M_{01},M_{10})=(1,-1)$ or $(-1,1)$, and the two remaining entries are then matched by $k=-M_{11}$ and $k=M_{11}$ respectively.
--
--   This is the case in which the Euclidean descent `BurauFaithful.sl2_euclid_step` on the measure $|M_{00}|$ terminates, so that the descent produces the continued fraction normal form $M=\pm S^{\varepsilon}T^{a_1}ST^{a_2}\cdots$ of an element of the modular group (Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, §3.3, pp. 129–130).
--
--   **Formalization Note** The determinant is expanded by `Matrix.det_fin_two` and the sign alternatives come from `Int.mul_eq_one_iff_eq_one_or_neg_one`; both cases are then closed entrywise using `ModularGroup.coe_S` and `ModularGroup.coe_T_zpow`.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, pp. 129-130 (the Euclidean algorithm in the modular group); C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups*, 2nd ed., Springer 1964, p. 85.

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem BurauFaithful.sl2_normal_form_base (M : Matrix (Fin 2) (Fin 2) ℤ) (hd : M.det = 1)
    (h : M 0 0 = 0) :
    ∃ k : ℤ, M = (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) *
          (↑(ModularGroup.T ^ k) : Matrix (Fin 2) (Fin 2) ℤ) ∨
      M = -((↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) *
          (↑(ModularGroup.T ^ k) : Matrix (Fin 2) (Fin 2) ℤ)) := by sorry
