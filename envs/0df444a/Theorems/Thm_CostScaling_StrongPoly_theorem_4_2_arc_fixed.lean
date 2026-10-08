-- Prove2me | Theorems.Thm_CostScaling_StrongPoly_theorem_4_2_arc_fixed
-- name    : CostScaling.StrongPoly.theorem_4_2_arc_fixed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:39.715549+00:00
-- url     : https://prove2.me/theorems/172fbdd0-9f46-4d85-9077-f9324ba8ecd3
-- title:
--   Theorem 4.2 — a large reduced cost fixes an arc across error parameters
-- statement:
--   Let $G=(V,E)$ be a circulation network with $n=|V|\ge2$ and $m=|E|\ge n-1$. Let $ε>0$ and $ε'\ge0$. Suppose a circulation $f$ is ε-optimal with respect to a price function $p$, and an arc $(v,w)\in E$ satisfies
--
--   $$
--   |c_p(v,w)|\ge n(ε+ε').
--   $$
--
--   Then for every ε′-optimal circulation $f'$,
--
--   $$
--   f(v,w)=f'(v,w).
--   $$
--
--   This gives the arc-fixing criterion that underlies Corollary 4.3 and the progress statement of Lemma 4.4.
--
--   **Formalization Note** The bounds $n\ge2$ and $m\ge n-1$ are the standing network assumption on p. 5; $ε'\ge0$ is required by the paper's definition of an error parameter. Lean's reused reduced cost has $+p(v)-p(w)$ instead of the paper's $-p(v)+p(w)$; substituting $-p$ leaves both optimality and the absolute-value test unchanged.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Theorem 4.2, p. 16; standing network assumption p. 5

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 4.2, p. 16: an arc with a sufficiently large absolute reduced cost
has the same flow in a given `ε`-optimal circulation and every `ε'`-optimal
circulation. The paper's standing `m ≥ n - 1 ≥ 1` is explicit. -/
theorem theorem_4_2_arc_fixed (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ |reducedCost N p v w|) :
    ∀ f' : V → V → ℝ, IsEpsOptimal N f' ε' → f v w = f' v w := by sorry

end CostScaling.StrongPoly
