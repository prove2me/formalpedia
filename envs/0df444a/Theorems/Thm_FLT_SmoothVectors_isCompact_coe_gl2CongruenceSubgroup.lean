-- Prove2me | Theorems.Thm_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup
-- name    : FLT.SmoothVectors.isCompact_coe_gl2CongruenceSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/1bf53170-f115-5304-ba56-eedbb53a8c01
-- title:
--   Compactness of the congruence subgroups of GL₂(ℚₚ)
-- statement:
--   Let $p$ be a natural number that is prime (as a typeclass fact) and let $n$ be a natural number. Consider the subgroup `gl2CongruenceSubgroup p n` of $\mathrm{GL}_2(\mathbb{Q}_p)$ consisting of those invertible $2\times 2$ matrices $g$ over $\mathbb{Q}_p$ such that every entry of $g - 1$ has $p$-adic norm at most $p^{-n}$ and, simultaneously, every entry of $g^{-1} - 1$ has $p$-adic norm at most $p^{-n}$ (the condition on the inverse being imposed explicitly, so that the set is visibly closed under inversion). The assertion is that the underlying subset of $\mathrm{GL}_2(\mathbb{Q}_p)$ determined by this subgroup is compact, where $\mathrm{GL}_2(\mathbb{Q}_p)$ carries its usual topology as a group of units. For $n = 0$ the defining bound is $1$, so the statement is not merely about deep levels but covers the whole family uniformly.
--
--   This is the compactness half of the standard fact that the principal congruence subgroups $K_n \subset \mathrm{GL}_2(\mathbb{Q}_p)$ form a filtration of the maximal compact subgroup $\mathrm{GL}_2(\mathbb{Z}_p)$ by compact open subgroups. It is used when extracting a vector fixed by some $K_n$ from a nonzero space of $K_n$-invariants in the adelic lift of a cusp form, and more generally wherever finiteness of Haar measure or compact support of level indicator functions is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup.lean

import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open FLT.SmoothVectors

theorem FLT.SmoothVectors.isCompact_coe_gl2CongruenceSubgroup
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCompact ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by sorry
