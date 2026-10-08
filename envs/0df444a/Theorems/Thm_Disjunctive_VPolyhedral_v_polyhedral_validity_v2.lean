-- Prove2me | Theorems.Thm_Disjunctive_VPolyhedral_v_polyhedral_validity_v2
-- name    : Disjunctive.VPolyhedral.v_polyhedral_validity_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:49.132079+00:00
-- url     : https://prove2.me/theorems/59967de6-5f2d-4649-b0f0-96392cb2a955
-- title:
--   Proposition 12.1 — validity for a V-polyhedral disjunctive set via vertices and rays (nonempty disjuncts)
-- statement:
--   This is Proposition 12.1 of Balas's *Disjunctive Programming*, opening Chapter 12.
--
--   Let $Q$ be a finite index set and, for each $h\in Q$, let $P^h := \mathrm{conv}\,V^h + \mathrm{cone}\,R^h$ with finite, **nonempty** vertex set $V^h$ and finite ray set $R^h$; let $F := \bigcup_{h\in Q}P^h$. Then the inequality $\alpha x \ge \beta$ is valid for $F$ if and only if $\alpha p \ge \beta$ for every $p\in V^h$ and $\alpha r\ge 0$ for every $r \in R^h$, for every $h\in Q$.
--
--   **Formalization Note.** The retired version allowed a disjunct with no vertices. Then $P^h=\emptyset$ while its rays still constrained $\alpha$, which makes the equivalence false. The book's disjuncts are nonempty polyhedra, so every $V^h$ is nonempty; this is now the instance hypothesis `[∀ h, Nonempty (Vidx h)]`. The finiteness of $Q$ (`[Fintype Q]`) is the book's convention. The vertices and rays are given as finite indexed families `vpt h`, `rvec h`.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §12, p. 195, Proposition 12.1

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

namespace Disjunctive.VPolyhedral

/-- Proposition 12.1 (Balas, *Disjunctive Programming*, Springer 2018, §12, p. 195): for the
V-polyhedral disjunctive set `F := ⋃_{h∈Q} P^h`, `P^h = conv V^h + cone R^h`, over a finite index
set `Q` whose disjuncts are all nonempty (every `V^h ≠ ∅`), the inequality `αx ≥ β` is valid for
`F` if and only if `αp ≥ β` for every `p ∈ V^h` and `αr ≥ 0` for every `r ∈ R^h`, `h ∈ Q`.

Correction w.r.t. the retired version: the book's standing assumption that every disjunct
`P^h` is nonempty (has at least one vertex) is now the instance hypothesis
`[∀ h, Nonempty (Vidx h)]`; with `V^h = ∅` the set `P^h` is empty while its rays still
constrain `α`. -/
theorem v_polyhedral_validity_v2 {n : ℕ} {Q : Type*} [Fintype Q] (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] [∀ h, Nonempty (Vidx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ) :
    (∀ x ∈ DisjSet Vidx Ridx vpt rvec, beta ≤ dotProduct alpha x) ↔
      IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta := by sorry

end Disjunctive.VPolyhedral
