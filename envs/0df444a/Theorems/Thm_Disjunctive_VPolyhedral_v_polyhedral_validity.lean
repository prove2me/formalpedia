-- Prove2me | Theorems.Thm_Disjunctive_VPolyhedral_v_polyhedral_validity
-- name    : Disjunctive.VPolyhedral.v_polyhedral_validity
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:06:05.159144+00:00
-- url     : https://prove2.me/theorems/cc2cb483-154f-42c5-94f7-5341bbc0f6e1
-- title:
--   Proposition 12.1 — the V-polyhedral validity characterization
-- statement:
--   This is Proposition 12.1 of Balas's *Disjunctive Programming*, opening Chapter 12: validity
--   of a cut for a disjunctive set is exactly validity for each disjunct's vertices and rays.
--
--   Given the V-polyhedral representation $F = \bigcup_{h\in Q} P^h$, $P^h = \mathrm{conv}\,V^h +
--   \mathrm{cone}\,R^h$, the inequality $\alpha x \ge \beta$ is valid for $F$ if and only if
--   $\alpha p \ge \beta$ for every vertex $p \in V^h$ and $\alpha r \ge 0$ for every extreme ray
--   $r \in R^h$, over every disjunct $h \in Q$.
--
--   The book's proof is immediate from the representation: $\alpha x\ge\beta$ is valid for $F$
--   iff valid for every $P^h$, and validity for $P^h = \mathrm{conv}\,V^h+\mathrm{cone}\,R^h$
--   reduces exactly to validity on its (finitely many) generators. The book also notes the polar
--   reading: the family of valid inequalities for $F$ is the reverse polar $F^\#_\beta$, and since
--   $F$ is a union, polarity turns the union into an intersection of the individual $(P^h)^\#_\beta$.
--
--   **Formalization Note.** Stated as a genuine `Iff`, matching the proposition's own "if and only
--   if"; both directions are needed downstream (validity is used both to *check* a candidate cut
--   and to *construct* one from its restriction to known vertices/rays, as in the iterative
--   procedure of Fig. 12.1).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 195, Proposition 12.1

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

namespace Disjunctive.VPolyhedral

/-- Proposition 12.1 (Balas §12, p. 195): the inequality `αx≥β` is valid for `F := ⋃_h P^h` if
and only if `αp≥β` for every `p ∈ V^h` and `αr≥0` for every `r ∈ R^h`, for every `h ∈ Q`. -/
theorem v_polyhedral_validity {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ) :
    (∀ x ∈ DisjSet Vidx Ridx vpt rvec, beta ≤ dotProduct alpha x) ↔
      IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta := by sorry

end Disjunctive.VPolyhedral
