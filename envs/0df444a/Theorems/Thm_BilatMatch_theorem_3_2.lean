-- Prove2me | Theorems.Thm_BilatMatch_theorem_3_2
-- name    : BilatMatch.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:03.986977+00:00
-- url     : https://prove2.me/theorems/d1d209f1-01f0-447a-81a4-607d1a7477e2
-- title:
--   Theorem 3.2 (Edge-by-Edge Composition) — typewise bounds $\ell^\kappa_{\alpha,e,\omega}\ge\beta\,\mathbb E[(v-c_j)_+1\{c_j\in\kappa\}]$ give $V_\alpha(\mathcal I)\ge\beta\,\mathrm{FB}(\mathcal I)$
-- statement:
--   Fix $\alpha,\beta\ge0$ and an independent matching market $\mathcal I$ with finitely many agents, downward-closed feasibility, and report domains that are finite ordered sets or bounded intervals. Suppose that for every edge $e=(i,j)$ and residual profile $\omega$ a cap-compatible family $\{z^\kappa_{e,\omega}\}$ is given such that, for every initial seller cap $\kappa$ and buyer report $v$,
--   $$\ell^\kappa_{\alpha,e,\omega}(v)\ \ge\ \beta\,\mathbb E_{c_j}\big[(v-c_j)_+1\{c_j\in\kappa\}\big].$$
--   Then
--   $$V_\alpha(\mathcal I)\ \ge\ \beta\,\mathrm{FB}(\mathcal I).$$
--
--   This is the composition step: per-edge, per-cap bilateral guarantees combine into a guarantee for the whole matching market.
--
--   **Formalization Note** $V_\alpha(\mathcal I)$ uses the report domains (BIC and IIR for types and reports in them). $\mathrm{FB}(\mathcal I)$ is finite because all types are bounded.
--
--   Differences from the source:
--   - encoding: families indexed by the edge and the residual profile ω = θ_{-ij} → families indexed by the edge and a full in-domain profile ω, required for every such ω; reason: the two hypotheses are equivalent: compose with forgetting the i- and j-coordinates, or fix those coordinates
--   - encoding: report domains that are finite ordered sets or bounded intervals → each domain is a nonempty finite set or an interval [L, U] that carries the agent's prior; reason: types lie in their report domains
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Theorem 3.2, p.9 (pdf p.11)

import Mathlib
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB
import Definitions.Def_BilatMatch_typewise

open MeasureTheory

namespace BilatMatch

/-- **Theorem 3.2 (Edge-by-Edge Composition).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Theorem 3.2, p.9 (pdf p.11).

Fix `α, β ≥ 0` and an independent matching market `I` with finitely many agents, downward-closed
feasibility, and report domains that are finite ordered sets or bounded intervals. Suppose that for
every edge `e = (i, j)` and residual profile `ω` a cap-compatible family `{z^κ_{e,ω}}` is given with
`ℓ^κ_{α,e,ω}(v) ≥ β E_{c_j}[(v − c_j)_+ 1{c_j ∈ κ}]` for every initial seller cap `κ` and buyer report
`v`. Then `V_α(I) ≥ β FB(I)`.

**Formalization Note**
* Report domains `D u` satisfy `IsAuxDomain` (finite nonempty or `[L, U]`, carrying the prior's mass);
  `V_α(I)` is `ValphaOn I D α` (BIC/IIR for types and reports in the domains).
* The family is indexed by the edge and a full profile `ω` in the domains; it is required for every
  such `ω`. A family indexed by residual profiles is the same thing (compose with forgetting the
  `i`-, `j`-coordinates; conversely fix those coordinates).
* `ℓ^κ_{α,e,ω}(v)` is `typewise` (eq. (5)) with the original seller prior; `FB(I)` is finite since
  all types are bounded. -/
theorem theorem_3_2 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) {B S : Type*} [Fintype B] [Fintype S]
    (I : Market B S) (hI : I.IsValid) (D : B ⊕ S → Set ℝ)
    (hD : ∀ u, IsAuxDomain (Sum.elim I.buyerLaw I.sellerLaw u) (D u))
    (z : B × S → Profile B S → Set ℝ → ℝ → ℝ → ℝ)
    (hz : ∀ e ∈ I.edges, ∀ ω ∈ domainProfiles D,
      IsCapCompatible (D (Sum.inl e.1)) (D (Sum.inr e.2)) (z e ω))
    (hbound : ∀ e ∈ I.edges, ∀ ω ∈ domainProfiles D, ∀ κ : Set ℝ, IsCap (D (Sum.inr e.2)) κ →
      ∀ v ∈ D (Sum.inl e.1),
        β * ∫ c in κ, max (v - c) 0 ∂(I.sellerLaw e.2) ≤
          typewise α (D (Sum.inl e.1)) (D (Sum.inr e.2)) (I.sellerLaw e.2) (z e ω κ) v) :
    ((β * (FB I).toReal : ℝ) : EReal) ≤ ValphaOn I D α := by sorry

end BilatMatch
