-- Prove2me | Theorems.Thm_AubinLipschitz_clarkeCone_subset_liminf_contingentCone
-- name    : AubinLipschitz.clarkeCone_subset_liminf_contingentCone
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:12.354602+00:00
-- url     : https://prove2.me/theorems/7271b910-c565-49c8-aefc-7e8ba20b6c64
-- title:
--   §1, (14) — the Clarke cone lies in the lim inf of nearby contingent cones (corrected: finite-dimensional space)
-- statement:
--   Let $K$ be a subset of a finite-dimensional normed space and $x_0\in K$. Then
--
--   $$
--   C_K(x_0)\subset\liminf_{x\to_K x_0}T_K(x):
--   $$
--
--   for every $v\in C_K(x_0)$ and $\varepsilon>0$ there is $\eta>0$ such that every $x\in K$ with $\|x-x_0\|\le\eta$ admits $w\in T_K(x)$ with $\|v-w\|\le\varepsilon$.
--
--   This is the step that transfers surjectivity of the Clarke derivative at one point to approximate surjectivity of the contingent derivatives at all nearby points of the graph.
--
--   Differences from the source:
--   - correction: X a Banach space (§1, p.7) → X finite dimensional; reason: the printed inclusion is false in a Banach space. Take X = ℝ × L¹(0,1) with the max norm, let K be the set of (t, φ1_[0,t]) with t ∈ [0,1], φ measurable, |φ(s)| = s a.e., and x₀ = (0,0), v = (1,0). From (t, φ1_[0,t]) the step h(1, s↦s·1_]t,t+h]/h) stays in K and the second component has norm t + h/2, so v ∈ C_K(x₀). At a point (t, f) of K with t > 0, a tangent (w, r) with w ≥ 1/2 would give difference quotients r_n → r in L¹ carrying mass at least t/4 on sets of measure tending to 0, which is impossible, so d(v, T_K(x)) ≥ 1/2. The proof of (15) uses compactness of the ball v₀ + εB.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §1, display (14), p.10

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeCone
import Definitions.Def_AubinLipschitz_contingentCone

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §1, display (14), p.10: `C_K(x₀) ⊂ lim inf_{x →_K x₀} T_K(x)`, in the form (9), p.9,
of the limit inferior: for `v ∈ C_K(x₀)` and `ε > 0` there is `η > 0` such that every `x ∈ K`
with `‖x − x₀‖ ≤ η` has a `w ∈ T_K(x)` with `‖v − w‖ ≤ ε`.

**Formalization Note** The space is finite dimensional. The paper's standing assumption in §1 is
a Banach space, but its proof of (15) uses compactness of the ball, and the printed inclusion
fails in `ℝ × L¹(0, 1)`; see the item's natural-language statement. -/
theorem clarkeCone_subset_liminf_contingentCone {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (x₀ : E) (hx₀ : x₀ ∈ K) (v : E) (hv : v ∈ clarkeCone K x₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ x ∈ K, ‖x - x₀‖ ≤ η → ∃ w ∈ contingentCone K x, ‖v - w‖ ≤ ε := by sorry

end AubinLipschitz
