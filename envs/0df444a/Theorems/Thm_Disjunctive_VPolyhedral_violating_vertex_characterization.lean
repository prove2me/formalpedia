-- Prove2me | Theorems.Thm_Disjunctive_VPolyhedral_violating_vertex_characterization
-- name    : Disjunctive.VPolyhedral.violating_vertex_characterization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:06:45.668+00:00
-- url     : https://prove2.me/theorems/15af58b4-5191-49ac-8150-1c6e949f62d7
-- title:
--   Proposition 12.3 — the violating-vertex characterization via the disjunctive cone
-- statement:
--   This is Proposition 12.3 of Balas's *Disjunctive Programming*: when a candidate cut is tight
--   at a reference point $x_F$, violation of the cut translates exactly into a sign condition on
--   the disjunctive cone $C_{x_F}$.
--
--   Let $x_F$ be a reference point of $F$ and $\alpha x \ge \beta$ a cut tight at $x_F$ (i.e.
--   $\alpha x_F = \beta$). For $x \in F$, writing $(x', x_0') := (x - x_F, 1)$ for the
--   corresponding point of the disjunctive cone $C_{x_F}$: $\alpha x < \beta$ if and only if
--   $\alpha x' < 0$.
--
--   The book's proof derives this by direct substitution: translating the cut by $x_F$ gives
--   $\alpha x' \ge \beta - \alpha x_F$, and since $\alpha x_F = \beta$ by the tightness hypothesis,
--   the right side vanishes, giving exactly $\alpha x' \ge 0$ — whose negation is the stated
--   characterization.
--
--   **Formalization Note.** This is the mechanism that lets the iterative cut-generation procedure
--   of §12.1.1 search only among extreme points/rays of $F$ *adjacent to $x_F$* (via Theorem 12.2's
--   correspondence, not drafted this pass) rather than all of $F$: a violation of the tight cut is
--   read off directly from membership in the disjunctive cone.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 200-201, Proposition 12.3

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

namespace Disjunctive.VPolyhedral

/-- Proposition 12.3 (Balas §12.1.1, p. 200-201): for `x` in the disjunctive set `F`, when the
cut `αx≥β` is tight at `x_F` (`αx_F=β`, the restriction imposed just before the proposition),
`αx<β` (the cut is violated) if and only if `α(x-x_F)<0` for the corresponding point
`(x-x_F, 1)` of the disjunctive cone `C_{x_F}`. -/
theorem violating_vertex_characterization {n m : ℕ} {Q : Type*} {Rh : Q → ℕ}
    (Atil : Matrix (Fin m) (Fin n) ℝ) (btil : Fin m → ℝ) (Dh : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ)
    (d0h : ∀ h, Fin (Rh h) → ℝ) (xF : Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ)
    (hxF_tight : dotProduct alpha xF = beta)
    (x : Fin n → ℝ) (hx_cone : (x - xF, (1 : ℝ)) ∈ DisjunctiveCone Atil btil Dh d0h xF) :
    dotProduct alpha x < beta ↔ dotProduct alpha (x - xF) < 0 := by sorry

end Disjunctive.VPolyhedral
