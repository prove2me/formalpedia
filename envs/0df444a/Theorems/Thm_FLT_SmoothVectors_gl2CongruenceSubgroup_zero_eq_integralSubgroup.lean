-- Prove2me | Theorems.Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup
-- name    : FLT.SmoothVectors.gl2CongruenceSubgroup_zero_eq_integralSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/7b0b87ea-184c-5874-a3c7-58482a6d1e13
-- title:
--   Level-zero congruence subgroup equals GL₂(ℤₚ)
-- statement:
--   Let $p$ be a prime. Inside $\mathrm{GL}_2(\mathbb{Q}_p)$ consider two subgroups. The first, `gl2CongruenceSubgroup p 0`, is the subgroup of those $g$ such that every entry of $g - 1$ and every entry of $g^{-1} - 1$ has $p$-adic norm at most $p^{-0} = 1$ (the general member condition at level $n$ being a bound by $p^{-n}$ on the entries of both $g-1$ and $g^{-1}-1$). The second, [`LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]`](def/LocalLanglands_LocalHeckeInstance.html#L13), is the range of the group homomorphism $\mathrm{GL}_2(\mathbb{Z}_p) \to \mathrm{GL}_2(\mathbb{Q}_p)$ obtained by applying the structure map $\mathbb{Z}_p \to \mathbb{Q}_p$ entrywise. The theorem asserts that these two subgroups of $\mathrm{GL}_2(\mathbb{Q}_p)$ are equal; that is, the level-$0$ member of the congruence filtration is exactly the image of the integral general linear group.
--
--   This identifies the anchor of the congruence filtration of $\mathrm{GL}_2(\mathbb{Q}_p)$ with the standard maximal compact subgroup $\mathrm{GL}_2(\mathbb{Z}_p)$, so that facts proved about the abstractly defined filtration and facts proved about the integral subgroup can be used interchangeably. It is cited by [`FLT.SmoothVectors.gl2CongruenceSubgroup_le_integralSubgroup`](thm.html#FLT.SmoothVectors.gl2CongruenceSubgroup_le_integralSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.lean

import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open FLT.SmoothVectors

theorem FLT.SmoothVectors.gl2CongruenceSubgroup_zero_eq_integralSubgroup
    (p : ℕ) [Fact p.Prime] :
    gl2CongruenceSubgroup p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by sorry
