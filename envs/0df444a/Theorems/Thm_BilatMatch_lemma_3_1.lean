-- Prove2me | Theorems.Thm_BilatMatch_lemma_3_1
-- name    : BilatMatch.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:10.022477+00:00
-- url     : https://prove2.me/theorems/221e462b-0706-4486-a6a3-cf51e0ca22de
-- title:
--   Lemma 3.1 (Nested First-Best Caps) — $\kappa_{e,\omega}(v)$ is initial and increasing in $v$
-- statement:
--   Let a market have finitely many agents and a nonempty downward-closed family of matchings, and let $M^*$ be the canonical first-best matching (maximum gains from trade, then fewest edges, then a fixed report-independent order). For every edge $e$ and residual profile $\omega$, the first-best cap $\kappa_{e,\omega}(v)=\{c: e\in M^*(v,c,\omega)\}$ is an initial set of seller reports, and
--   $$\kappa_{e,\omega}(v)\subseteq\kappa_{e,\omega}(v')\qquad\text{whenever }v\le v'.$$
--
--   The nesting is what lets bilateral rules indexed by caps be composed into a monotone, hence implementable, matching allocation.
--
--   **Formalization Note** Seller reports range over all of $\mathbb R$, so "initial" means a lower set of $\mathbb R$.
--
--   Differences from the source:
--   - generalization: initial set of seller reports (reports in the auxiliary market's domain) → lower set of ℝ, for reports anywhere in ℝ; reason: M* is defined at every real profile; a lower set of ℝ intersected with any report domain is an initial set of that domain
--   - encoding: fixed, report-independent tie-breaking order → an injective rank on F; reason: every strict order on a finite family is induced by an injective rank
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma 3.1, p.8 (pdf p.10)

import Mathlib
import Definitions.Def_BilatMatch_canonicalMax

open MeasureTheory

namespace BilatMatch

/-- **Lemma 3.1 (Nested First-Best Caps).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Lemma 3.1, p.8 (pdf p.10).

For every edge `e = (i, j)` and residual profile `ω`, the first-best cap
`κ_{e,ω}(v) = {c : e ∈ M*(v, c, ω)}` is an initial set of seller reports, and
`κ_{e,ω}(v) ⊆ κ_{e,ω}(v')` whenever `v ≤ v'`.

**Formalization Note** `M*` is the canonical first-best matching of p.8 (maximum gains from trade,
then fewest edges, then a fixed injective rank on `F`). Seller reports range over all of `ℝ`, so
"initial set" is `IsLowerSet`. The residual profile `ω` is a full profile whose `i`- and
`j`-coordinates are ignored. -/
theorem lemma_3_1 {B S : Type*} [Fintype B] [Fintype S] (I : Market B S) (hI : I.IsValid)
    (rank : Set (B × S) → ℕ) (hrank : IsTieOrder I rank) (e : B × S) (ω : Profile B S) :
    (∀ v : ℝ, IsLowerSet (firstBestCap I rank e ω v)) ∧
    (∀ v v' : ℝ, v ≤ v' → firstBestCap I rank e ω v ⊆ firstBestCap I rank e ω v') := by sorry

end BilatMatch
