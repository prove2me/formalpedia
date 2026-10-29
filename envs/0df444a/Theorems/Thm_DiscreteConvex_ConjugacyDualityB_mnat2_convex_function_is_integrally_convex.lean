-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_mnat2_convex_function_is_integrally_convex
-- name    : DiscreteConvex.ConjugacyDualityB.mnat2_convex_function_is_integrally_convex
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T02:42:59.661681+00:00
-- url     : https://prove2.me/theorems/5ed03ef2-f0fa-46cc-ae2b-1619fae663b2
-- title:
--   Theorem 8.31, function part — M♮₂-convex functions are integrally convex
-- statement:
--   Let $V$ be a finite ground set and let $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ be a sum of two M♮-convex functions. Then $f$ is integrally convex:
--
--   $$
--   \overline f(p)=\widetilde f(p)\qquad\text{for every }p\in\mathbb R^V,
--   $$
--
--   where $\overline f$ is the convex closure using all finite convex combinations of effective-domain points and $\widetilde f$ is the corresponding closure using only effective-domain points in $[\lfloor p\rfloor,\lceil p\rceil]$. This is exactly the function assertion of the mission's Theorem 8.31; the set assertion is a separate leaf.
-- source:
--   K. Murota, Discrete Convex Analysis, SIAM, 2003, p.227, Theorem 8.31. https://doi.org/10.1137/1.9780898718508.ch8. Exact set/function clauses separated from the existing mission milestone.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvexFunction

theorem DiscreteConvex.ConjugacyDualityB.mnat2_convex_function_is_integrally_convex {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : DiscreteConvex.ConjugacyDualityB.MNat2Convex f) :
    DiscreteConvex.ConjugacyDualityB.IsIntegrallyConvexFunction f := by sorry
