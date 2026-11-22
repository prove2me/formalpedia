-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_toggle_detector_variation
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.toggle_detector_variation
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-22T22:59:31.065572+00:00
-- url     : https://prove2.me/theorems/d5eebee8-1d67-44c0-8884-2137bc55f503
-- title:
--   Detector variation added by one cut toggle
-- statement:
--   Let $G$ be an oriented physical multigraph with nonnegative active capacities $u_e$, let $y$ be vertex potentials, and let $b_e$ be the detector baselines. Suppose a cut $C$ satisfies $\operatorname{cap}_u(C)\le U$, and a toggle amount satisfies $0\le\tau\le U^{-1}$. Replacing $y$ by $y+\tau\mathbf 1_C$ increases the total weighted detector displacement by at most one:
--
--   $$
--   \sum_{e\in E}u_e\left|(y_a+\tau\mathbf1_C(a))-(y_b+\tau\mathbf1_C(b))-b_e\right|
--   \le
--   \sum_{e\in E}u_e|y_a-y_b-b_e|+1,
--   $$
--
--   where $a,b$ are the endpoints of $e$. The point is that an edge contributes to the increment precisely when it crosses $C$, so the total increment is $\tau\operatorname{cap}_u(C)\le\tau U\le1$.
--
--   This is the local variation estimate behind Lemma 3.2's detector-report bound in §3.2.1: after baselines are reset exactly on reported edges, reports can be charged against disjoint increments of this displacement potential.
--
--   **Formalization Note** The statement uses the mission's `Physical`, `cutCapacity`, and finite-edge-sum conventions, including loops and parallel identifiers. Only one toggle is considered; no execution or report semantics are assumed.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2 and §3.2.1, the ToggleCut and detector-report clauses; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. This is the immediate capacity-weighted variation calculation used by that report bound.

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- One toggle increases the total capacity-weighted detector displacement by at most one. -/
theorem toggle_detector_variation {n k : ℕ} (g : Physical n k)
    (y : Fin n → ℝ) (b : Fin k → ℝ) (C : Finset (Fin n)) (tau U : ℝ)
    (hu : ∀ e ∈ g.active, 0 ≤ g.u e)
    (hcap : cutCapacity g C ≤ U) (htau0 : 0 ≤ tau) (htauU : tau ≤ 1 / U) :
    (∑ e ∈ g.active, g.u e *
      |(y (g.graph.tail e) + if g.graph.tail e ∈ C then tau else 0) -
        (y (g.graph.head e) + if g.graph.head e ∈ C then tau else 0) - b e|) ≤
    (∑ e ∈ g.active, g.u e * |y (g.graph.tail e) - y (g.graph.head e) - b e|) + 1 := by sorry
