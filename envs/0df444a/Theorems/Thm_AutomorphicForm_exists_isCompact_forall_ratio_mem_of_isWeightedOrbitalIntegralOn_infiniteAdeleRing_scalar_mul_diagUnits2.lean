-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3ab25cbc-21c4-536e-b827-f87c82fefd06
-- title:
--   Non-vanishing archimedean weighted orbital values confine the ratio a
-- statement:
--   Let $K$ be a number field and let $K_\infty$ denote its infinite adele ring, so that $\mathrm{GL}_2(K_\infty)$ carries the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57). Let $\nu$ be a measure on $\mathrm{GL}_2(K_\infty)$ for that $\sigma$-algebra, let $wt : \mathrm{GL}_2(K_\infty) \to \mathbb{R}$ be a weight function, and let $fa : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ have compact support. Then there is a compact subset $C$ of the unit group $(K_\infty)^\times$ with the following property. Let $a, b \in (K_\infty)^\times$ and put $\gamma = b\cdot I_2 \cdot \mathrm{diag}(a,1)$, the product of the scalar matrix with entry $b$ and the invertible diagonal matrix `diagUnits2 a 1` with diagonal entries $a$ and $1$. Let $\tau$ be a measure on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_\infty)$ (Borel $\sigma$-algebra) and let $J \in \mathbb{C}$. Suppose $J$ is a weighted orbital integral value of $fa$ at $\gamma$ relative to $(\nu, \tau, wt)$, that is: there is $s : \mathrm{GL}_2(K_\infty) \to \mathbb{R}$ which is everywhere non-negative, measurable and compactly supported, satisfies $\int_{Z(\gamma)} s(tx)\,d\tau(t) = 1$ for every $x$ with $fa(x^{-1}\gamma x) \neq 0$, and for which $J = \int fa(x^{-1}\gamma x)\, wt(x)\, s(x)\, d\nu(x)$. If $J \neq 0$ then $a \in C$. In particular $C$ depends only on $\nu$, $wt$ and $fa$, uniformly in $b$, in $\tau$ and in the section function $s$.
--
--   This is the archimedean support bound for weighted orbital integrals along the family $b\,\mathrm{diag}(a,1)$: a non-zero value forces some conjugate of $b\,\mathrm{diag}(a,1)$ into the compact support of the test function, and the conjugation invariant $\mathrm{tr}^2/\det = a + 2 + a^{-1}$, which is independent of $b$, then confines $a$ to a compact subset of $(K_\infty)^\times$. It is used by [`AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem`](thm.html#AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem) to cut the global sum over torus parameters down to finitely many terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isWeightedOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (wt : GL (Fin 2) (InfiniteAdeleRing K) → ℝ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : HasCompactSupport fa) :
    ∃ C : Set (InfiniteAdeleRing K)ˣ, IsCompact C ∧
      ∀ (a b : (InfiniteAdeleRing K)ˣ)
        (τ : Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
        (J : ℂ),
        AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν wt
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) τ fa J → J ≠ 0 → a ∈ C := by sorry
