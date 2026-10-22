-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_strictMonoOn
-- name    : BirkhoffGlobalSection.birkhoff_far_arc_strictMonoOn
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-26T21:37:12.788636+00:00
-- url     : https://prove2.me/theorems/c369c5d0-aa7d-4875-8c31-f9c51c6007d3
-- title:
--   Strict horizontal monotonicity along a far shooting arc
-- statement:
--   Let $\varphi$ be a Levi-Civita Hamiltonian flow on the selected energy component, let $s$ be a state, and suppose its forward trajectory is a far shooting arc of length $\tau$. Its horizontal position relative to the primary is strictly increasing throughout the closed time interval:
--
--   $$
--   0\le t_1<t_2\le\tau\quad\Longrightarrow\quad
--   x_1(\varphi_{t_1}s)<x_1(\varphi_{t_2}s).
--   $$
--
--   The far-arc hypotheses include strict negativity of the vertical position in the interior, a terminal crossing of the vertical line below the axis, and positive horizontal Jacobi velocity after the start. This supplies the monotone-sweep clause in the crossing-curve construction and implies uniqueness of its crossing time.
--
--   **Formalization Note** No additional restrictions on the real parameters $\mu,c$ are required beyond the assumed Hamiltonian flow and arc. The statement uses the existing `IsFarShootingArc` predicate.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S5, Section 5, proof of Theorem 5.1, far-family property (ii). Coordinate derivation from Joung--van Koert, https://arxiv.org/abs/2407.19159v3, equation (2.2). Extracted from the monotonicity calculation in Prove2Me submission 412e5116-4ecc-452a-8339-e8ad5d85fb00 using the proved explicit-gradient theorem.

import Definitions.Def_BirkhoffShootingArcs

open BirkhoffGlobalSection

set_option autoImplicit false

theorem BirkhoffGlobalSection.birkhoff_far_arc_strictMonoOn (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (τ : ℝ)
    (h : IsFarShootingArc φ x τ) :
    StrictMonoOn
      (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
      (Set.Icc 0 τ) := by sorry
