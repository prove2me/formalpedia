-- Prove2me | Theorems.Thm_AutomorphicForm_mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one
-- name    : AutomorphicForm.mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/f034f666-82ad-5ba8-95ce-d42c01ee7770
-- title:
--   Twisted centraliser of a diagonal δ with norm ratio ≠ 1
-- statement:
--   Let $L/F$ be a finite Galois extension of fields, and let $\sigma \in \mathrm{Gal}(L/F)$ be such that every $F$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $\delta \in \mathrm{GL}_2(L)$ have vanishing off-diagonal entries, $\delta_{10} = 0$ and $\delta_{01} = 0$, and assume that the field norm $N_{L/F}(\delta_{00}/\delta_{11})$ is different from $1$. Write $\sigma$ also for the automorphism of $\mathrm{GL}_2(L)$ obtained by applying the ring homomorphism underlying $\sigma$ to each matrix entry. Then for every $t \in \mathrm{GL}_2(L)$, the element $t$ lies in the $\sigma$-twisted centraliser of $\delta$, that is, $t\,\delta\,\sigma(t)^{-1} = \delta$ (the subgroup `sigmaCentralizer` being defined by exactly this equation), if and only if $t_{10} = 0$, $t_{01} = 0$, and both diagonal entries $t_{00}$ and $t_{11}$ lie in the image of the structure map $F \to L$. Thus the twisted centraliser is the group of diagonal matrices in $\mathrm{GL}_2(L)$ with entries drawn from $F$.
--
--   This is the computation of the $\sigma$-twisted centraliser of a diagonal element of hyperbolic norm type in $\mathrm{GL}_2(L)$ for a cyclic extension $L/F$: it is the split diagonal torus over the base field, which is the group over whose points the corresponding twisted orbital integral in the twisted trace formula for base change is fibred. It is used in the estimate [`AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one`](thm.html#AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one) comparing twisted orbital integrals of indicator functions of semi-local integral sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_SigmaCentralizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hN : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (t : Matrix.GeneralLinearGroup (Fin 2) L) :
    t ∈ AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ ↔
      (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) L) 0 0 ∈ Set.range (algebraMap F L) ∧
        (t : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap F L) := by sorry
