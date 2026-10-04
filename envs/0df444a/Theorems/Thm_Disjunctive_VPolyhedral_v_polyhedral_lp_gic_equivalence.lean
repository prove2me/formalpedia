-- Prove2me | Theorems.Thm_Disjunctive_VPolyhedral_v_polyhedral_lp_gic_equivalence
-- name    : Disjunctive.VPolyhedral.v_polyhedral_lp_gic_equivalence
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:07:53.537269+00:00
-- url     : https://prove2.me/theorems/bb6ba5fa-a20e-48c1-b7e7-1f2f2397e868
-- title:
--   Theorem 12.5 — the three-way cut-family equivalence
-- statement:
--   This is Theorem 12.5 of Balas's *Disjunctive Programming*, the goal theorem of this mission
--   and the capstone that unifies all three cut families the book has developed: **V-polyhedral
--   cuts, lift-and-project cuts, and generalized intersection cuts are equivalent.**
--
--   The V-polyhedral cuts $\alpha x \ge \beta$ satisfying the point-ray system (12.8) coincide
--   exactly with the lift-and-project cuts arising from feasible solutions
--   $(\alpha,\beta,\{u^h\}_{h\in Q})$ of the cut-generating LP (12.9), and these in turn coincide
--   with the generalized intersection cuts from the $P_I$-free polyhedron
--   $$
--   S := \{x \in \mathbb{R}^n : u^h \tilde D^h x \le u^h \tilde d^h_0,\ h \in Q\}
--   $$
--   built from the very same multipliers $u^h$.
--
--   The book's two-line proof: the first equivalence holds because both (12.8) and (12.9)
--   describe validity for the same convex set $\mathrm{conv}\bigcup_h \tilde P^h$ — one via its
--   generators (vertices/rays), the other via its supporting-hyperplane (dual/CGLP) description;
--   the second equivalence is the general equivalence of GICs to their corresponding L&P cuts
--   (Theorem 11.5 of `11a-intersection-cuts`, restated locally here). The book remarks that,
--   despite the superficial resemblance to the GIC-defining system (11.5), the two systems are
--   genuinely different: the points of (11.5) lie on the boundary of $S$, while the vertices of
--   (12.8) typically lie outside $S$ — yet the two systems yield equivalent cuts.
--
--   **Formalization Note.** The equivalence is packaged as a single `Iff`: `(α,β)` is
--   `IsVPolyhedralValid` if and only if there exists a multiplier vector `u` making it
--   simultaneously CGLP-(12.9)-feasible *and* a GIC from `S`(`u`) — directly capturing that all
--   three characterizations describe the same set of cuts, with `S` built from the *same* `u` that
--   witnesses the CGLP leg, matching the theorem's own "from the same solution's multipliers"
--   reading. `IsGICFromS`'s two conditions (valid outside `int S`, genuine cut) are the exact
--   characterization Theorem 11.4's own remark gives for the GIC family, avoiding a full
--   re-derivation of Chapter 11's extreme-ray machinery here.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 207, Theorem 12.5

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

namespace Disjunctive.VPolyhedral

/-- Theorem 12.5 (Balas §12.2, p. 207), the goal theorem of this mission: the V-polyhedral cuts
`αx≥β` valid for the combined system (12.8) are equivalent to the lift-and-project cuts from
feasible solutions of the CGLP (12.9), which are in turn equivalent to the generalized
intersection cuts from the `P_I`-free set `S := {x : ū^hD̃^hx ≤ ū^hd̃^h_0, h∈Q}` built from the
same solution's multipliers. `(D̃^h, d̃^h_0)` describes the same polyhedron as the V-polyhedral
data `(v^h, r^h)` (`hDesc`), the cut is one that `x̄ ∈ P` violates, and the equivalence is up to
the positive scaling that (12.9)'s normalization `Σu = 1` fixes. Without these the two sides
speak of unrelated data: `(α,β) = (0,-1)` is valid on the left and impossible on the right, and
an unnormalized `(α,β)` can never match `Σu = 1`. -/
theorem v_polyhedral_lp_gic_equivalence {n : ℕ} {Q : Type*} [Fintype Q] {Rh : Q → ℕ}
    (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ)
    (Dtil : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ) (d0til : ∀ h, Fin (Rh h) → ℝ)
    (hDesc : ∀ h, {x : Fin n → ℝ | ∀ i, d0til h i ≤ ((Dtil h).mulVec x) i} =
      {x : Fin n → ℝ | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
        ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r})
    (P : Set (Fin n → ℝ)) (xbar : Fin n → ℝ) (hxbar : xbar ∈ P)
    (alpha : Fin n → ℝ) (beta : ℝ) (hviol : dotProduct alpha xbar < beta) :
    IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta ↔
      ∃ (t : ℝ) (u : ∀ h, Fin (Rh h) → ℝ), 0 < t ∧
        IsCGLP129Feasible Dtil d0til (t • alpha) u (t * beta) ∧
        IsGICFromS Dtil d0til P u (t • alpha) (t * beta) := by sorry

end Disjunctive.VPolyhedral
