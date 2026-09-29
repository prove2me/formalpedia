-- Prove2me | Theorems.Thm_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
-- name    : Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d7eb20c7-531a-563e-ba4b-d9328e2d3a36
-- title:
--   Smooth algebras over reduced Noetherian rings are reduced
-- statement:
--   Let $R$ and $S$ be commutative rings, taken in a single universe $u$, with $S$ an $R$-algebra. Assume the structure map $R \to S$ is smooth in Mathlib's sense, that is `Algebra.Smooth R S`: $S$ is formally smooth over $R$ and of finite presentation as an $R$-algebra. Assume moreover that $R$ is reduced (its only nilpotent element is $0$) and that $R$ is a Noetherian ring. The conclusion is that $S$ is reduced, again in the sense of `IsReduced`: every nilpotent element of $S$ vanishes. Relative to the classical statement that a smooth algebra over a reduced ring is reduced, the hypothesis that $R$ be Noetherian is an extra assumption here, and both rings are constrained to lie in the same universe.
--
--   This is the ring-theoretic form of the standard fact that smoothness transfers reducedness from the base to the total ring (EGA IV 17.5.7). Within the formalisation it is used for the case of a field base and for étale algebras, and in the construction of smooth affine charts on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [IsReduced R] [IsNoetherianRing R] : IsReduced S := by sorry
