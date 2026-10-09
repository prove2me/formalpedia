-- Prove2me | Theorems.Thm_DRConvexOpt_Reform_boundary_step
-- name    : DRConvexOpt.Reform.boundary_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:32.684989+00:00
-- url     : https://prove2.me/theorems/47850f17-1214-4963-a704-6795f7536e2a
-- title:
--   Proof of Theorem 1, pp. 35–36 — the i-th dual constraint holds on C̄_i iff it holds on all of C_i
-- statement:
--   Let the confidence sets $\mathcal C_i$ of (5) be defined by proper cones, let $\mathcal C_I$ be bounded and contain every $\mathcal C_i$, assume (N) and $P + Q \ge 1$. Let $v$ satisfy (C3), and fix $x$, an index $i$, $\beta \in \mathbb R^K$ and $\kappa, \lambda \in \mathbb R^I$. Put
--   $$g(z,u) = v(x,z) - [Az + Bu]^\top\beta - \sum_{i' \in \mathcal A(i)} [\kappa_{i'} - \lambda_{i'}].$$
--   Then
--   $$g(z,u) \le 0 \ \ \forall (z,u) \in \overline{\mathcal C}_i \quad\Longleftrightarrow\quad g(z,u) \le 0 \ \ \forall (z,u) \in \mathcal C_i.$$
--
--   The step removes the descendants $\mathcal C_{i'}$, $i' \in \mathcal D(i)$, from the constraint set again, so that Lemma 1 can be applied to the conic set $\mathcal C_i$ itself.
--
--   **Formalization Note** As in the partition step, $\mathcal C_i \subseteq \mathcal C_I$ and $P + Q \ge 1$ are added: in dimension zero $\overline{\mathcal C}_i$ can be empty while $\mathcal C_i$ is not. The paper's argument (a convex function attains its maximum on the boundary, and the boundary of $\overline{\mathcal C}_i$ is that of $\mathcal C_i$) is not part of the statement.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 35–36, proof of Theorem 1: the reformulation of the i-th constraint over C̄_i and the boundary argument

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Reform

open MeasureTheory Matrix

/-- Proof of Theorem 1, pp. 35–36: the `i`-th constraint
`v(x, z) − [Az + Bu]ᵀβ − Σ_{i' ∈ 𝒜(i)} [κ_{i'} − λ_{i'}] ≤ 0` holds on `C̄_i` iff it holds on all
of `C_i`. Disclosed additions: every `C_i` lies in `C_I`, and `P + Q > 0`. -/
theorem boundary_step {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hbdd : Bornology.IsBounded (d.conf (Fin.last nI)))
    (hN : Nesting d) (hsub : ∀ i, d.conf i ⊆ d.conf (Fin.last nI)) (hdim : 0 < nP + nQ)
    (x : Fin nN → ℝ) (i : Fin (nI + 1)) (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ) :
    (∀ ω ∈ cbar d i, v.eval x ω.1 - (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β -
        ∑ i' ∈ anc d i, (κ i' - lam i') ≤ 0) ↔
    (∀ ω ∈ d.conf i, v.eval x ω.1 - (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β -
        ∑ i' ∈ anc d i, (κ i' - lam i') ≤ 0) := by sorry

end DRConvexOpt.Reform
