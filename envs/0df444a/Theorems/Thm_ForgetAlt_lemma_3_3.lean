-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_3
-- name    : ForgetAlt.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:50.856656+00:00
-- url     : https://prove2.me/theorems/77cfdbdd-7b3a-42d5-8654-0c79c48f5b3e
-- title:
--   Lemma 3.3: properties (P1)–(P3) of candidate parents and $\mathrm{dist}^\alpha$
-- statement:
--   Let $u$ be a vertex of the ABD $H$ (reachable from $f$). Then:
--
--   1. **(P1)** for every $u'\in P(u)$, $\mathrm{dist}^\alpha(u)>\mathrm{dist}^\alpha(u')$;
--   2. **(P2)** for every neighbour $u'$ of $u$,
--   $$u'\in P(u)\iff \rho(\{u',u\})=\overline{\alpha(u)}\ \text{and}\ \mathrm{dist}^{\overline{\alpha(u)}}(u')+1=\mathrm{dist}^\alpha(u),$$
--   where $\overline{\alpha(u)}$ is the parity other than $\alpha(u)$;
--   3. **(P3)** for every edge $e=\{u',u\}$, $\mathrm{dist}^{\rho(e)}(u')+1\ge\mathrm{dist}^\alpha(u)$, with strict inequality if $e\notin E^+_H(u)$.
--
--   In particular $\mathrm{dist}^\alpha$ strictly decreases along every directed path of $H$, so $H$ is a DAG.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: u ∈ V(H) → u reachable from f; reason: V(H) is the reachable set (Definition 3.2)
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.3, printed p.17 (PDF p.18)

import Mathlib
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.3**, printed p.17 (PDF p.18). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"For any `u ∈ V(H)`, the following properties hold (for `u = f`, (P1) and (P2) are vacuous since
`P(f) = ∅`): (P1) For any `u′ ∈ P(u)`, `dist^α(u) > dist^α(u′)` holds. … (P2) For any neighbor
`u′` of `u`, `u′ ∈ P(u)` holds if and only if both `ρ({u′, u}) = ᾱ(u)` and
`dist^{ᾱ(u)}(u′) + 1 = dist^α(u)` hold. (P3) For any edge `e = {u′, u}`,
`dist^{ρ(e)}(u′) + 1 ≥ dist^α(u)` holds. The inequality is strict if `e ∉ E⁺_H(u)`."

**Formalization Note.** In (P2) the page prints overlined parities, `ᾱ(u)` (the other parity,
`(alpha G M u).flip`); the text layer drops the bars. `u ∈ V(H)` is reachability from `f`; neighbours and edges are those of
the extended system; distances in `ℕ∞`. -/
theorem lemma_3_3 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (u : ExtV V) (hu : Reach G M u) :
    (∀ u' ∈ candParents G M u, distA G M u' < distA G M u) ∧
    (∀ u', (extGraph G M).Adj u' u →
      (u' ∈ candParents G M u ↔
        rho G M s(u', u) = (alpha G M u).flip ∧ dist G M (alpha G M u).flip u' + 1 = distA G M u)) ∧
    (∀ u', (extGraph G M).Adj u' u →
      distA G M u ≤ dist G M (rho G M s(u', u)) u' + 1 ∧
      (s(u', u) ∉ EplusH G M u → distA G M u < dist G M (rho G M s(u', u)) u' + 1)) := by sorry

end ForgetAlt
