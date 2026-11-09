-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_17
-- name    : ForgetAlt.lemma_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:26:53.179491+00:00
-- url     : https://prove2.me/theorems/b02f13e7-95ea-4cc2-87dc-f75100ab563d
-- title:
--   Lemma 3.17: the converted path meets the same postdominator classes as the double path
-- statement:
--   Let $(P,Q,y,z)$ be any double path of $(H,E^*)$, $T$ any ABT respecting it (with any fixed MIEs), and $X$ the output of $\textsc{PathConstruction}(T,r_T(y),r_T(z),\mathrm{odd},\{y,z\})$. Then a postdominator class of $H_0$ meets $V(X)$ if and only if it meets $V(P)\cup V(Q)$.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: ℓ, with 2ℓ + 1 the length of a shortest augmenting path (|U| ≥ 2 assumed throughout) → hypothesis HasAugPath M; reason: ℓ is undefined when (G, M) has no augmenting path; the hypothesis only excludes that case
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.17, printed p.27 (PDF p.28)

import Mathlib
import Definitions.Def_ForgetAlt_DoublePathABD

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.17**, printed p.27 (PDF p.28). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `(P, Q, y, z)` be any double path, `T` be any ABT respecting `(P, Q, y, z)`, and `X` be the
output of `PathConstruction(T, r_T(y), r_T(z), odd, {y, z})`. Then a postdominator class
intersects `V(X)` if and only if it intersects `V(P) ∪ V(Q)`."

**Formalization Note.** Double paths are those of `(H, E*)` (Definition 3.11); `e*_T` is any MIE
choice; classes are those of `H₀`, named by their roots `r`. -/
theorem lemma_3_17 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (hA : HasAugPath M) (d : List V × List V × V × V) (hd : IsDoublePathABD G M (InEstar G M) d)
    (par : ExtV V → ExtV V) (hT : IsABT G M par) (hresp : RespectsDP par d)
    (mie : ExtV V → Sym2 (ExtV V)) (hmie : MIEChoice G M par mie) (L : List (ExtV V))
    (hL : PCReturns G M par mie (rootFree G M par (.orig d.2.2.1)) (rootFree G M par (.orig d.2.2.2))
      .odd s(.orig d.2.2.1, .orig d.2.2.2) L) (r : V) :
    (∃ w : V, ExtV.orig w ∈ L ∧ cl (h0Adj G M) w = r) ↔
      (∃ w ∈ dpVerts d, cl (h0Adj G M) w = r) := by sorry

end ForgetAlt
