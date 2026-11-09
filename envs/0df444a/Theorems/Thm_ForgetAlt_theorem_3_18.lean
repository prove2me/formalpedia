-- Prove2me | Theorems.Thm_ForgetAlt_theorem_3_18
-- name    : ForgetAlt.theorem_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:28.39224+00:00
-- url     : https://prove2.me/theorems/d7542126-4e21-41bd-ab7f-0dcfe2c40d1f
-- title:
--   Theorem 3.18 (Structure Theorem): $\mathrm{Aug}(D)$ of a maximal $D$ is a maximal set of disjoint shortest augmenting paths
-- statement:
--   Let $D$ be a set of vertex-disjoint double paths of $(H,E^*)$. An ABT respecting all members of $D$ exists, and for every such ABT $T$ and every choice of MIEs, $\mathrm{Aug}(D)$ is a set of vertex-disjoint shortest augmenting paths. If $D$ is maximal, then
--
--   $$\mathrm{Aug}(D)\ \text{is a maximal set of disjoint shortest augmenting paths.}$$
--
--   This is the core of Theorem 1.1: maximality of the alternation-free packing transfers to the augmenting paths.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: ℓ, with 2ℓ + 1 the length of a shortest augmenting path (|U| ≥ 2 assumed throughout) → hypothesis HasAugPath M; reason: ℓ is undefined when (G, M) has no augmenting path; the hypothesis only excludes that case
--   - generalization: Theorem 3.18 (maximal D ⇒ Aug(D) maximal) → also: a respecting ABT exists, and Aug(D) is a disjoint shortest-augmenting family for every vertex-disjoint D; reason: these are the claims of pp.23–24 that make Aug(D) well defined; the maximal case is the theorem
--   - reading: Aug(D), defined with “a single ABT respecting all of them” → the conclusion for every ABT respecting all members and every MIE choice; reason: the strong reading of a construction that leaves T and the MIEs free
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Theorem 3.18, printed p.27 (PDF p.28); Section 3.5, printed p.24 (PDF p.25)

import Mathlib
import Definitions.Def_ForgetAlt_DoublePathABD

namespace ForgetAlt

open BergeMatching.Core

/-- **Theorem 3.18** (Structure Theorem), printed p.27 (PDF p.28). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"For any maximal set `D` of vertex-disjoint double paths of `(H, E*)`, `Aug(D)` is a maximal set
of disjoint shortest augmenting paths."

Together with the definition of `Aug(D)` (Section 3.5, p.24): an ABT respecting all double paths
of a vertex-disjoint set `D` exists, and for every such ABT and every MIE choice, applying
`PathConstruction` to each member gives a set of disjoint shortest augmenting paths.

**Formalization Note.** `Aug(D)` is stated for **every** ABT respecting all members and every MIE
choice (`IsAugOf`); the first conjunct covers every vertex-disjoint `D`, the second adds
maximality when `D` is maximal. -/
theorem theorem_3_18 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (hA : HasAugPath M) (D : List (List V × List V × V × V))
    (hD : IsDisjointDPFamilyABD G M (InEstar G M) D) :
    (∃ par, IsABT G M par ∧ ∀ d ∈ D, RespectsDP par d) ∧
    ∀ par : ExtV V → ExtV V, IsABT G M par → (∀ d ∈ D, RespectsDP par d) →
      ∀ mie : ExtV V → Sym2 (ExtV V), MIEChoice G M par mie →
        ∃ A : List (List V), IsAugOf G M par mie D A ∧ IsDisjointSAPFamily M A ∧
          (IsMaximalDPFamilyABD G M (InEstar G M) D → IsMaximalSAPFamily M A) := by sorry

end ForgetAlt
