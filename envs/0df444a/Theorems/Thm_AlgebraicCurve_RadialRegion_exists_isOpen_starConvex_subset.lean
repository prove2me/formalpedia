-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset
-- name    : AlgebraicCurve.RadialRegion.exists_isOpen_starConvex_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/cd27b438-f87a-5a76-84b5-851b3bccb411
-- title:
--   Star-convex open neighbourhood of a radial region
-- statement:
--   Let $R$ be a radial datum: a centre $R.q \in \mathbb{C}$, a continuous function $r : \mathbb{R} \to \mathbb{R}$ that is periodic with period $2\pi$ and strictly positive at every angle, together with a natural number $N$ and a strictly monotone family $\varphi_0 < \varphi_1 < \dots < \varphi_N$ of reals indexed by `Fin (N + 1)` with $\varphi_0 = 0$ and $\varphi_N = 2\pi$, such that $r$ is twice continuously differentiable on each closed subinterval $[\varphi_i, \varphi_{i+1}]$. Write $R.K \subseteq \mathbb{C}$ for the region attached to $R$. Let $T \subseteq \mathbb{C}$ be an open set containing $R.K$. The assertion is that there is a set $V \subseteq \mathbb{C}$ which is open, contains the centre $R.q$, is star-convex with respect to $R.q$ over $\mathbb{R}$ (for every $x \in V$ and all reals $a, b \ge 0$ with $a + b = 1$ one has $a\,R.q + b\,x \in V$, i.e. the real segment from $R.q$ to $x$ lies in $V$), and satisfies $R.K \subseteq V \subseteq T$.
--
--   This interpolates an open star-shaped domain between a radial region and any open set containing it, which is what makes the elementary existence theory for primitives of holomorphic functions on star-shaped domains applicable on a neighbourhood of the region. It is used in the cell-dissection treatment of path integrals, in particular in the construction of local primitives with prescribed jumps and in the period-and-residue decomposition of integrals over the dissection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.RadialRegion.exists_isOpen_starConvex_subset (R : RadialRegion) (T : Set ℂ)
    (hT : IsOpen T) (hKT : R.K ⊆ T) :
    ∃ V : Set ℂ, IsOpen V ∧ R.q ∈ V ∧ StarConvex ℝ R.q V ∧ R.K ⊆ V ∧ V ⊆ T := by sorry
