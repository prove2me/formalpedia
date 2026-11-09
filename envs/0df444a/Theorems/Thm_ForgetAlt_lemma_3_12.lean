-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_12
-- name    : ForgetAlt.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:55.118303+00:00
-- url     : https://prove2.me/theorems/2971bc54-38b2-45b7-9d49-8e9dcd5744b9
-- title:
--   Lemma 3.12: shortest augmenting paths have volumes at most $2\ell+5$
-- statement:
--   Let $X$ be any shortest augmenting path. Then every edge of $X$ has volume at most $2\ell+5$, every vertex $v$ of $X$ satisfies $\mathrm{vlevel}(v)\le 2\ell+5$, and in particular
--
--   $$\mathrm{dist}^\alpha(v)\le\ell+2\qquad(v\in V(X)).$$
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.12, printed p.23 (PDF p.24)

import Mathlib
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.12**, printed p.23 (PDF p.24). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Any shortest augmenting path `X` contains no edge of volume larger than `2ℓ + 5`, i.e.,
`vlevel(X) ≤ 2ℓ + 5`, and every vertex `v` of `X` satisfies `vlevel(v) ≤ 2ℓ + 5`. In particular,
`dist^α(v) ≤ ℓ + 2`." -/
theorem lemma_3_12 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    {u v : V} (X : G.Walk u v) (hX : IsShortestAugPath M X) :
    (∀ e ∈ X.edges, vlevelE G M (e.map .orig) ≤ ((2 * ell M + 5 : ℕ) : ℕ∞)) ∧
    (∀ w ∈ X.support, vlevelV G M (.orig w) ≤ ((2 * ell M + 5 : ℕ) : ℕ∞)) ∧
    (∀ w ∈ X.support, distA G M (.orig w) ≤ ((ell M + 2 : ℕ) : ℕ∞)) := by sorry

end ForgetAlt
