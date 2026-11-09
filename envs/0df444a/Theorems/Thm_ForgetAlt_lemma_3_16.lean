-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_16
-- name    : ForgetAlt.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:41.48556+00:00
-- url     : https://prove2.me/theorems/d52cc793-a428-4699-a30f-e0411d3b10ee
-- title:
--   Lemma 3.16: shortest augmenting paths visit postdominator classes like double paths
-- statement:
--   Let $P$ be any shortest augmenting path from $u_1$ to $u_2$. Then:
--
--   1. $P$ contains exactly one edge $e_P=\{y,z\}\in E^*$, with $u_1,y,z,u_2$ in this order along $P$;
--   2. for every postdominator class $C(r)$ of $H_0$ meeting $V(P)$, $P$ contains $r$, and $V(P)\cap C(r)$ induces a subpath of $P$;
--   3. there is a double path $(Y,Z,y,z)$ with $Y$ from $y$ to $u_1$ and $Z$ from $z$ to $u_2$ all of whose vertices lie in postdominator classes meeting $V(P)$.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - reading: V(P) ∩ C(r) induces a subpath of P → the positions of P lying in C(r) form an interval; reason: P is a path, so its induced subpaths are its contiguous segments
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.16, printed p.26 (PDF p.27)

import Mathlib
import Definitions.Def_ForgetAlt_DoublePathABD

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.16**, printed p.26 (PDF p.27). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `P` be any shortest augmenting path from `u₁` to `u₂`. Then the following properties hold.
(i) `P` contains exactly one edge `e_P = {y, z}` in `E*`, where `u₁, y, z, u₂` appear in this order
along `P`. (ii) For every postdominator class `C(r)` intersecting `V(P)`, `P` contains `r`, and
`V(P) ∩ C(r)` induces a subpath of `P`. (iii) There exists a double path `(Y, Z, y, z)`, where `Y`
is a path from `y` to `u₁` and `Z` is a path from `z` to `u₂`, such that every vertex of `Y` and
`Z` belongs to a postdominator class intersecting `V(P)`."

**Formalization Note.** Classes are those of `H₀` (`cl (h0Adj G M)`). "Induces a subpath": the
positions of `P` in `C(r)` form an interval `[i, j]`. The double path of (iii) is for the edge
`{y, z}` of (i). -/
theorem lemma_3_16 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    {u₁ u₂ : V} (P : G.Walk u₁ u₂) (hP : IsShortestAugPath M P) :
    (∃ (i : ℕ) (y z : V), P.support[i]? = some y ∧ P.support[i + 1]? = some z ∧
      InEstar G M y z ∧
      (∀ (j : ℕ) (w w' : V), j ≠ i → P.support[j]? = some w → P.support[j + 1]? = some w' →
        ¬ InEstar G M w w') ∧
      ∃ Y Z : List V, IsDoublePathABD G M (InEstar G M) (Y, Z, y, z) ∧
        Y.getLast? = some u₁ ∧ Z.getLast? = some u₂ ∧
        ∀ w ∈ Y ++ Z, ∃ w' ∈ P.support, cl (h0Adj G M) w = cl (h0Adj G M) w') ∧
    (∀ r : V, (∃ w ∈ P.support, cl (h0Adj G M) w = r) →
      r ∈ P.support ∧ ∃ i j : ℕ, ∀ k : ℕ,
        (∃ w, P.support[k]? = some w ∧ cl (h0Adj G M) w = r) ↔ (i ≤ k ∧ k ≤ j)) := by sorry

end ForgetAlt
