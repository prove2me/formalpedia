-- Prove2me | Theorems.Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth
-- name    : Algebra.IsSmoothAt.of_isSmoothAt_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/81ce274e-c76e-5414-acd9-de98e11bc7ad
-- title:
--   Smoothness at a prime descends along a smooth algebra
-- statement:
--   Let $R$, $S$, $T$ be commutative rings in a fixed universe, with $S$ an $R$-algebra, $T$ an $S$-algebra and $T$ an $R$-algebra, these structures forming a scalar tower, and assume that $S$ is of finite presentation as an $R$-algebra and that $T$ is a smooth $S$-algebra (formally smooth and of finite presentation over $S$). Let $\mathfrak P$ be a prime ideal of $T$ such that $R \to T$ is smooth at $\mathfrak P$ in the sense of `Algebra.IsSmoothAt`, that is, the localisation $T_{\mathfrak P}$ is a formally smooth $R$-algebra, and let $\mathfrak p$ be a prime ideal of $S$ which is the ideal lying under $\mathfrak P$, i.e. the preimage of $\mathfrak P$ along the structure map $S \to T$ equals $\mathfrak p$. Then $R \to S$ is smooth at $\mathfrak p$: the localisation $S_{\mathfrak p}$ is a formally smooth $R$-algebra.
--
--   This is the ring-theoretic core of the descent of smoothness through a smooth morphism, as in EGA IV 17.7.7. It is used in the scheme-level statement [`AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.IsSmoothAt.of_isSmoothAt_of_smooth (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FinitePresentation R S] [Algebra.Smooth S T] (𝔓 : Ideal T) [𝔓.IsPrime]
    (h : Algebra.IsSmoothAt R 𝔓) (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔓.under S = 𝔭) :
    Algebra.IsSmoothAt R 𝔭 := by sorry
