-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_15
-- name    : ForgetAlt.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:49.419717+00:00
-- url     : https://prove2.me/theorems/99964f78-4069-407b-9413-be126451382e
-- title:
--   Lemma 3.15 (down-up property) of shortest augmenting paths
-- statement:
--   Let $X$ be any shortest augmenting path from $u_1$ to $u_2$. Then $X$ contains exactly one critical edge $e_X=\{y,z\}$ of volume $2\ell+5$, with $u_1,y,z,u_2$ in this order along $X$, and $e_X\in E^*$. Moreover, every other edge $\{w,w'\}$ of volume $2\ell+5$ in $X$, with $w$ before $w'$, satisfies
--
--   $$w\in P(w')\ \text{if it precedes } e_X,\qquad w'\in P(w)\ \text{if it follows } e_X.$$
--
--   So $X$ traverses its volume-$(2\ell+5)$ edges downward in the ABD before $e_X$ and upward after it.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: “exactly one critical edge of volume 2ℓ + 5” → an edge at position i with these properties, and every other edge of volume 2ℓ + 5 is not critical; reason: positions in the vertex list of X give the order along X
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.15, printed p.25 (PDF p.26)

import Mathlib
import Definitions.Def_ForgetAlt_DoublePathABD

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.15** (Down-up property), printed p.25 (PDF p.26). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `X` be any shortest augmenting path from `u₁` to `u₂` (`u₁, u₂ ∈ U`). Then `X` contains
exactly one critical edge `e_X = {y, z}` of volume `2ℓ + 5`, where `u₁, y, z, u₂` appear in this
order along `X`, and `e_X ∈ E*` holds. Moreover, every other edge `{w, w′}` of volume `2ℓ + 5`
in `X`, where `w` precedes `w′` along `X`, satisfies `w ∈ P(w′)` if it precedes `e_X`, and
`w′ ∈ P(w)` if it follows `e_X`."

**Formalization Note.** Edges of `X` are consecutive entries `(X[j], X[j+1])` of its vertex list;
`e_X` is at position `i`. "Exactly one" is: every other edge of volume `2ℓ + 5` is not critical. -/
theorem lemma_3_15 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    {u₁ u₂ : V} (X : G.Walk u₁ u₂) (hX : IsShortestAugPath M X) :
    ∃ (i : ℕ) (y z : V), X.support[i]? = some y ∧ X.support[i + 1]? = some z ∧
      IsCritical G M s(.orig y, .orig z) ∧
      vlevelE G M s(.orig y, .orig z) = ((2 * ell M + 5 : ℕ) : ℕ∞) ∧ InEstar G M y z ∧
      ∀ (j : ℕ) (w w' : V), j ≠ i → X.support[j]? = some w → X.support[j + 1]? = some w' →
        vlevelE G M s(.orig w, .orig w') = ((2 * ell M + 5 : ℕ) : ℕ∞) →
          ¬ IsCritical G M s(.orig w, .orig w') ∧
          (j < i → ExtV.orig w ∈ candParents G M (.orig w')) ∧
          (i < j → ExtV.orig w' ∈ candParents G M (.orig w)) := by sorry

end ForgetAlt
