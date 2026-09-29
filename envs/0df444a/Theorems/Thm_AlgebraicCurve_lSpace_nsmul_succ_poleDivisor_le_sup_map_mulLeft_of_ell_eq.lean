-- Prove2me | Theorems.Thm_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
-- name    : AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/a4ad21af-5975-53ea-8caf-8936737643dc
-- title:
--   Stabilisation of the pole filtration past the Riemann–Roch threshold
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $x \in F$, and let $D$ be a divisor of $F/K$, i.e. a finitely supported function from the places of $F/K$ (valuation subrings of $F$ containing the image of $K$, distinct from $F$ itself and principal ideal rings) to $\mathbb{Z}$. Assume $D$ is the pole divisor of $x$: for every place $v$, $D(v) = \max(0, -\operatorname{ord}_v x)$, where $\operatorname{ord}_v$ is minus the logarithm of the associated adic valuation. Assume further that for every natural number $M$ the space $\mathcal{L}(M \cdot D) = \{f \in F : v(f) \le \exp(M \cdot D(v)) \text{ for all } v\}$ is finite-dimensional over $K$, and that there are natural numbers $M_0, d, g_0$ with $\dim_K \mathcal{L}(N \cdot D) = N d + 1 - g_0$ (as an identity of integers) for every natural $N \ge M_0$. Then for every natural number $m$ with $m \ge M_0 + 1$ one has the inclusion of $K$-subspaces of $F$
--   $$\mathcal{L}((m+1) \cdot D) \le \mathcal{L}(m \cdot D) + x \cdot \mathcal{L}(m \cdot D),$$
--   the second summand being the image of $\mathcal{L}(m \cdot D)$ under the $K$-linear map of multiplication by $x$.
--
--   This is the stabilisation step for the filtration of $F$ by the Riemann–Roch spaces of the multiples of the pole divisor of $x$: once the dimension formula $\ell(N\cdot D) = Nd + 1 - g_0$ has set in, multiplication by $x$ carries the $m$-th graded piece onto the $(m+1)$-st. It is used in the construction of a basis adapted to this filtration ([`AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor`](thm.html#AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor)) and in [`AlgebraicCurve.exists_forall_mem_span_pow_mul_of_forall_ord_nonneg`](thm.html#AlgebraicCurve.exists_forall_mem_span_pow_mul_of_forall_ord_nonneg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    (m : ℕ) (hm : M₀ + 1 ≤ m) :
    (LSpace ((m + 1) • D) : Submodule K F)
      ≤ LSpace (m • D) ⊔ (LSpace (m • D)).map (LinearMap.mulLeft K x) := by sorry
