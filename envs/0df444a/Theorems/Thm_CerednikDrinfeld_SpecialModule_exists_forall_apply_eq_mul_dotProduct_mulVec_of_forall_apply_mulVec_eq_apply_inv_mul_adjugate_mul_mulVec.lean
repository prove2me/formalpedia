-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec
-- name    : CerednikDrinfeld.SpecialModule.exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/8c93020b-fd96-5180-9c77-5e925627ecf4
-- title:
--   ⋆-balanced bilinear forms on k² are multiples of Jμ
-- statement:
--   Let $k$ be a field and let $\mu \in M_2(k)$ be a matrix with $\operatorname{tr}\mu = 0$ and $\det\mu \neq 0$. Let $b \colon k^2 \to k^2 \to k$ be a $k$-bilinear form (a $k$-linear map from $k^2$ to the space of $k$-linear maps $k^2 \to k$), and assume that $b$ is balanced for the involution $x \mapsto \mu^{-1}\operatorname{adj}(x)\mu$ on $2 \times 2$ matrices, in the sense that for every $x \in M_2(k)$ and all $v, w \in k^2$ one has $b(xv, w) = b\bigl(v, (\mu^{-1}\operatorname{adj}(x)\mu)w\bigr)$, where $\operatorname{adj}$ is the adjugate and $\mu^{-1}$ is the Mathlib nonsingular inverse. The conclusion is that there exists a scalar $c \in k$ such that for all $v, w \in k^2$, $b(v,w) = c \cdot \bigl(v \cdot (J\mu)w\bigr)$, the product being the dot product on $k^2$ and $J = \begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}$. No symmetry or nondegeneracy of $b$ is assumed, and the scalar $c$ is not asserted to be nonzero.
--
--   This identifies the space of bilinear forms on the standard $M_2(k)$-module that are balanced for the $\mu$-twisted adjugate involution as the line spanned by $(v,w) \mapsto v^{\mathsf T}(J\mu)w$, in every characteristic. It is used in the Čerednik–Drinfeld part of the development, in the vanishing statement [`CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.eq_zero_of_eq_smul_tmul_sub_tmul_of_forall_map_eq_map_star_of_isSplit_of_charP), where a pairing on a split quaternionic module is pinned down after transport to the standard module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.SpecialModule.exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec
    (k : Type) [Field k] (μ : Matrix (Fin 2) (Fin 2) k) (htr : μ.trace = 0) (hdet : μ.det ≠ 0)
    (b : (Fin 2 → k) →ₗ[k] (Fin 2 → k) →ₗ[k] k)
    (hb : ∀ (x : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k),
      b (x.mulVec v) w = b v ((μ⁻¹ * x.adjugate * μ).mulVec w)) :
    ∃ c : k, ∀ v w : Fin 2 → k,
      b v w = c * dotProduct v ((!![0, 1; -1, 0] * μ).mulVec w) := by sorry
