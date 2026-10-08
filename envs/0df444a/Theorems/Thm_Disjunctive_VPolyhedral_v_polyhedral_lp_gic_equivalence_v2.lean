-- Prove2me | Theorems.Thm_Disjunctive_VPolyhedral_v_polyhedral_lp_gic_equivalence_v2
-- name    : Disjunctive.VPolyhedral.v_polyhedral_lp_gic_equivalence_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:46.729847+00:00
-- url     : https://prove2.me/theorems/de5b6388-9bab-4f07-814f-4e3069aceb5a
-- title:
--   Theorem 12.5 — V-polyhedral cuts, CGLP (12.9) cuts and generalized intersection cuts coincide (nonempty disjuncts)
-- statement:
--   This is Theorem 12.5 of Balas's *Disjunctive Programming*, the goal theorem of the mission. It unifies V-polyhedral cuts, lift-and-project cuts and generalized intersection cuts.
--
--   Let $Q \neq \emptyset$ be finite. For each $h\in Q$ let the relaxed disjunct $\tilde P^h = \{x : \tilde D^h x \ge \tilde d^h_0\}$ coincide with $\mathrm{conv}\,\tilde V^h + \mathrm{cone}\,\tilde R^h$, where $\tilde V^h \ne\emptyset$ (every disjunct is nonempty). Let $\bar x \in P$ and let $\alpha x\ge\beta$ be a cut with $\alpha\bar x<\beta$. Then the following are equivalent:
--
--   1. $(\alpha,\beta)$ satisfies the point-ray system (12.8), i.e. $\alpha p \ge \beta$ for all $p\in\tilde V^h$ and $\alpha r\ge0$ for all $r\in\tilde R^h$, $h\in Q$;
--   2. for some $t>0$ and multipliers $u = \{u^h\}_{h\in Q}$, the scaled cut $(t\alpha, t\beta)$ together with $u$ is feasible for the cut-generating LP (12.9):
--   $$t\alpha = u^h\tilde D^h,\quad t\beta \le u^h\tilde d^h_0\ (h\in Q),\quad \textstyle\sum_{h\in Q}u^he = 1,\quad u\ge0,$$
--   and the same $(t\alpha,t\beta)$ is a generalized intersection cut from $S := \{x : u^h\tilde D^hx \le u^h\tilde d^h_0,\ h\in Q\}$ relative to $P$: it is valid for every point of $P$ outside $\mathrm{int}\,S$ and violated by some point of $P$.
--
--   **Formalization Note.** The retired version allowed a disjunct with no vertices. Then both descriptions in `hDesc` could be the empty set, condition 1 held vacuously, and the CGLP forced $\alpha=0$. The book's disjuncts are nonempty and its disjunction has at least one term, so the new statement adds the instance hypotheses `[Nonempty Q]` and `[∀ h, Nonempty (Vidx h)]`. With $Q=\emptyset$ the normalization $\sum_h u^he=1$ is unsatisfiable. The rest is unchanged: the scaling $t>0$ accounts for the normalization of (12.9), and the generalized-intersection-cut property is the local characterization `IsGICFromS`.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §12.2, p. 207, Theorem 12.5

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

namespace Disjunctive.VPolyhedral

/-- Theorem 12.5 (Balas, *Disjunctive Programming*, Springer 2018, §12.2, p. 207), the goal
theorem of the mission: the V-polyhedral cuts `αx ≥ β` valid for the combined system (12.8) are
exactly (up to the positive scaling fixed by the normalization `Σ_h u^h e = 1` of (12.9)) the
lift-and-project cuts from feasible solutions of the CGLP (12.9), and these are the generalized
intersection cuts from `S := {x : u^h D̃^h x ≤ u^h d̃^h_0, h ∈ Q}` built from the same
multipliers. The disjunction has at least one term (`Q ≠ ∅`), every relaxed disjunct
`P̃^h = conv Ṽ^h + cone R̃^h = {x : D̃^h x ≥ d̃^h_0}` is nonempty (`Ṽ^h ≠ ∅`), and the cut is one
that the point `x̄ ∈ P` violates.

Correction w.r.t. the retired version: the book's standing assumptions that the disjunction has
a term and that every disjunct is nonempty are now the instance hypotheses `[Nonempty Q]` and
`[∀ h, Nonempty (Vidx h)]`; without them both sides of `hDesc` can be empty, making the left
side vacuous while the CGLP forces `α = 0`. -/
theorem v_polyhedral_lp_gic_equivalence_v2 {n : ℕ} {Q : Type*} [Fintype Q] [Nonempty Q]
    {Rh : Q → ℕ}
    (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)]
    [∀ h, Nonempty (Vidx h)]
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
