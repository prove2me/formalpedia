-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_standard_intersection_cuts_complete
-- name    : Disjunctive.GeneralDisjunctions.standard_intersection_cuts_complete
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:59:22.115429+00:00
-- url     : https://prove2.me/theorems/c6404557-45cc-439a-b666-991ebb7e5a44
-- title:
--   Theorem 11.2 — completeness of standard intersection cuts
-- statement:
--   This is Theorem 11.2 of Balas's *Disjunctive Programming*, cited to [25], the goal theorem
--   of this mission: **every facet of the integer hull that cuts off a vertex of the LP relaxation
--   is realized exactly by a standard intersection cut.**
--
--   Let $F$ be a facet of $\mathrm{conv}(P_I)$, defined by an inequality $\varphi x \ge \varphi_0$
--   valid on $P_I$ but violated by some point of $P$, and suppose $F$ cuts off a vertex $v$ of $P$
--   (i.e. $\varphi v < \varphi_0$). Then:
--
--   $$
--   T := \{x : \varphi x \le \varphi_0\} \text{ is } P_I\text{-free at } v, \qquad
--   \sum_{j\in J} \tfrac{1}{\lambda_j}\, x_j \ge 1 \;=\; \{x : \varphi_0 \le \varphi x\},
--   $$
--
--   where $J$ is $v$'s cobasis and $\lambda_j$ is the parameter at which the LP cone's $j$-th
--   extreme ray from $v$ exits $T$. In words: the standard intersection cut derived from $T$ at
--   $v$ is not merely *a* valid cut but *literally reconstructs* $F$'s own defining inequality.
--
--   The book's proof: since $\varphi x\ge\varphi_0$ is valid on $P_I$, the halfspace complement
--   $T$ has no $P_I$ point in its interior, i.e. $T$ is $P_I$-free; since $v\in\mathrm{int}\,T$,
--   Theorem 1.1 applies at $v$ with $S:=T$, and because $T$ is itself a single halfspace, every
--   extreme ray of the LP cone at $v$ exits $T$ through the *same* hyperplane $\varphi x=\varphi_0$,
--   so the resulting intersection cut is exactly that hyperplane.
--
--   **Formalization Note.** "Cuts off some vertex $v$ of $P$" is formalized directly as $v\in P$
--   together with $\varphi v<\varphi_0$ (rather than via a separate `IsVertex` predicate), since
--   $v$ is given as a basic solution via its cobasis $J$ (`hvJ`) — the same style
--   `01-intro-duality`'s Theorem 1.1 uses for its own basic solution. `hfacet` is included for
--   fidelity to the printed "facet" hypothesis even though the book's own two-line proof does not
--   use faciality beyond "cuts off a vertex" (see `MODERATION_NOTES.md`). The exit parameters
--   `lam` are hypothesized via `IsGreatest`, matching Theorem 1.1's own convention, rather than
--   assumed positive as a bare unjustified hypothesis.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 152, Theorem 11.2

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic

namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.2 (Balas §11.2, p. 152, [25]), the goal theorem of this mission: every facet of
`conv(P_I)`, defined by the inequality `φx≥φ0`, that cuts off some vertex `v` of `P` (i.e. `v`
violates it strictly), is defined by a standard intersection cut: the halfspace `T:={x:φx≤φ0}`
is `P_I`-free at `v`, and the intersection cut derived from `T` at `v` (basic index set `I`,
cobasis `J`, tableau `abar`, exit parameters `lam`) is exactly `{x:φ0≤φx}` itself. The ray is `v + t r^j`, the LP cone's own ray (as in Theorem 1.1),
`v` is a vertex of `P`, and `P_I ⊆ P ⊆ C(J)`; without the tie to `P` the completeness claim fails
(`P_I = ∅` makes `IsFacet ∅` vacuous and the cut comes out reversed). -/
theorem standard_intersection_cuts_complete {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ) (PI P : Set (ι → ℝ))
    (phi : ι → ℝ) (phi0 : ℝ) (lam : ι → ℝ)
    (hvP : v ∈ Set.extremePoints ℝ P) (hvJ : ∀ j ∈ J, v j = 0)
    (hPIsub : PI ⊆ P) (hPcone : ∀ x ∈ P, ∀ j ∈ J, 0 ≤ x j)
    (hvalid : ∀ x ∈ PI, phi0 ≤ dotProduct phi x)
    (hviolated : ∃ x ∈ P, dotProduct phi x < phi0)
    (hcutoff : dotProduct phi v < phi0)
    (hfacet : IsFacet (convexHull ℝ PI) {x ∈ convexHull ℝ PI | dotProduct phi x = phi0})
    (hlam_exit : ∀ j ∈ J,
      IsGreatest {t : ℝ | dotProduct phi (v + t • extremeRay I abar j) ≤ phi0} (lam j)) :
    PIFree {x | dotProduct phi x ≤ phi0} PI v ∧
      IntersectionCutSet J lam = {x | phi0 ≤ dotProduct phi x} := by sorry

end Disjunctive.GeneralDisjunctions
