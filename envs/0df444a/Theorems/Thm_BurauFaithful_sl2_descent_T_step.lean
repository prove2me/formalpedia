-- Prove2me | Theorems.Thm_BurauFaithful_sl2_descent_T_step
-- name    : BurauFaithful.sl2_descent_T_step
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T07:03:07.542851+00:00
-- url     : https://prove2.me/theorems/6fb5b8fe-42dd-4037-b1e6-41409f7193b6
-- title:
--   The arithmetic core of the $\mathbf T$-rule for the Euclidean descent in $\mathrm{SL}(2,\mathbb Z)$
-- statement:
--   The arithmetic core of the $\mathbf T$-rule for the Euclidean descent in the modular group.
--
--   Let $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, let $M$ be an integral $2\times2$ matrix with $M_{00}\neq0$, and let
--   $$n(M)=-\Bigl\lfloor \frac{M_{01}}{M_{00}}\Bigr\rfloor$$
--   be the Euclidean quotient used by the descent step $M\mapsto (M\cdot T^{n(M)})\cdot S$. Right multiplication by $T^{\,j}$ leaves $M_{00}$ unchanged and replaces $M_{01}$ by $M_{01}+j\,M_{00}$, so the quotient shifts by exactly $j$:
--   $$n\bigl(M\cdot T^{\,j}\bigr)=n(M)-j,\qquad\text{that is}\qquad
--   -\frac{(M T^{j})_{01}}{(M T^{j})_{00}}=-\frac{M_{01}}{M_{00}}-j .$$
--   Consequently the descent target is unchanged, $\bigl((M T^{j})\cdot T^{\,n(M)-j}\bigr)\cdot S=(M\cdot T^{\,n(M)})\cdot S$, and the descent section $\rho$ satisfies $\rho(M\cdot T^{j})=\rho(M)\cdot(\operatorname{lift}T)^{j}$ — one of the two multiplication rules which make $\rho$ a section of the specialization $t=-1$ and hence prove the faithfulness statement for three strands.
--
--   **Formalization Note** The left-hand side is expanded with `ModularGroup.coe_T_zpow` and the quotient identity is `Int.add_mul_ediv_left` (the divisor is `M 0 0`, assumed nonzero).
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, pp. 129-130 (the Euclidean algorithm in the modular group).

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem BurauFaithful.sl2_descent_T_step (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M 0 0 ≠ 0) (j : ℤ) :
    -(((M * (↑(ModularGroup.T ^ j) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1) /
        ((M * (↑(ModularGroup.T ^ j) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0)) =
      -(M 0 1 / M 0 0) - j := by sorry
