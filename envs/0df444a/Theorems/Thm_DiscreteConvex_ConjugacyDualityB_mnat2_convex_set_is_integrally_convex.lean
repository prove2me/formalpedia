-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_mnat2_convex_set_is_integrally_convex
-- name    : DiscreteConvex.ConjugacyDualityB.mnat2_convex_set_is_integrally_convex
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T02:42:48.220179+00:00
-- url     : https://prove2.me/theorems/8bee8c69-5440-45b7-ab12-de468ac9d8db
-- title:
--   Theorem 8.31, set part — M♮₂-convex sets are integrally convex
-- statement:
--   Let $V$ be a finite ground set and let $D\subseteq\mathbb Z^V$ be M♮₂-convex, meaning that $D$ is the intersection of two M♮-convex sets. Then $D$ is integrally convex: for every real vector $p$,
--
--   $$
--   p\in\operatorname{conv}(D)\ \Longrightarrow\ p\in\operatorname{conv}\bigl(D\cap[\lfloor p\rfloor,\lceil p\rceil]\bigr).
--   $$
--
--   This is the set assertion in Theorem 8.31, separated from the function assertion so it can be proved and reused independently. Empty sets and empty ground sets are included.
-- source:
--   K. Murota, Discrete Convex Analysis, SIAM, 2003, p.227, Theorem 8.31. https://doi.org/10.1137/1.9780898718508.ch8. Exact set/function clauses separated from the existing mission milestone.

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvex

theorem DiscreteConvex.ConjugacyDualityB.mnat2_convex_set_is_integrally_convex {V : Type*} [Fintype V] [DecidableEq V]
    (D : Set (V → ℤ)) (hD : DiscreteConvex.ConjugacyDualityB.MNat2ConvexSet D) :
    DiscreteConvex.ConjugacyDualityB.IsIntegrallyConvex D := by sorry
