-- Prove2me | Theorems.Thm_Dynamics_exists_smul_of_locally_exists_smul
-- name    : Dynamics.exists_smul_of_locally_exists_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T03:08:36.652668+00:00
-- url     : https://prove2.me/theorems/f77bc932-450f-40dc-8556-90c6bfe442e1
-- title:
--   Locally related by a group action implies globally related
-- statement:
--   Let a group $G$ act on a set $S$ and let $P:\mathbb R\to S$ be a family of points such that any two parameters closer than $\delta$ have their values in the same $G$-orbit:
--
--   $$
--   |t_0-t_1|<\delta\ \Longrightarrow\ \exists\,g\in G,\ P(t_0)=g\cdot P(t_1).
--   $$
--
--   Then *any* two parameters do: $P$ takes values in a single $G$-orbit.
--
--   **Role.** This is the monodromy step, in its bare form. A geometric object defined only locally — a chart, a frame, a lift — is typically pinned down only up to a symmetry group, and the question is whether the local ambiguities compose into a single global one. Over a connected parameter space they do, and over an interval the proof is a chaining argument: subdivide into steps shorter than $\delta$ and multiply the group elements together.
--
--   In the analysis of a closed local geodesic in a spherical building, $P(\theta)$ is the pair of vectors describing the curve as a great circle in the apartment chart around $\theta$, $G$ is the finite Weyl group, and the local hypothesis is the compatibility of overlapping apartment charts. The conclusion is that the descriptions at any two angles differ by a single Weyl element, which is what makes the transport around the full circle — the monodromy — an element of $W$.
--
--   Nothing is assumed about $S$ beyond the action: no topology, no metric, and no continuity of $P$. Only the parameter space is required to be an interval, and that only so that it can be subdivided.
-- source:
--   Standard monodromy argument. Used for the transport of local apartment descriptions around the circle in C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4.

import Mathlib

namespace Dynamics

theorem exists_smul_of_locally_exists_smul {G S : Type*} [Group G] [MulAction G S]
    (P : ℝ → S) (delta : ℝ) (hd : 0 < delta)
    (hloc : ∀ t0 t1 : ℝ, |t0 - t1| < delta → ∃ g : G, P t0 = g • P t1) :
    ∀ t0 t1 : ℝ, ∃ g : G, P t0 = g • P t1 := by sorry

end Dynamics
