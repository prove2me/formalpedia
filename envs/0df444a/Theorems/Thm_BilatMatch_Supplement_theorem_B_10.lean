-- Prove2me | Theorems.Thm_BilatMatch_Supplement_theorem_B_10
-- name    : BilatMatch.Supplement.theorem_B_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:30:44.376612+00:00
-- url     : https://prove2.me/theorems/a9327d97-9291-47cf-854d-31e9fd85d33b
-- title:
--   Theorem B.10 (Composition with Cap-Dependent Bounds) — $V_\alpha(\mathcal I)\ge\sum_e\mathbb E[T^{\kappa_{e,\omega}(v_i)}_{e,\omega}(v_i)]$
-- statement:
--   Fix $\alpha\ge0$ and an independent matching market $\mathcal I$ with finitely many agents and downward-closed feasibility, on report domains that are finite ordered sets or bounded intervals. For each edge $e=(i,j)$ and residual profile $\omega$, let $\{z^\kappa_{e,\omega}\}$ be a cap-compatible family, and let $T^\kappa_{e,\omega}(v)$ be typewise lower bounds with finite expectations and $T^\emptyset_{e,\omega}=0$. If
--   $$\ell^\kappa_{\alpha,e,\omega}(v)\ \ge\ T^\kappa_{e,\omega}(v)$$
--   for every edge $e$, residual profile $\omega$, initial seller cap $\kappa$ and buyer report $v$, then
--   $$V_\alpha(\mathcal I)\ \ge\ \sum_{e=(i,j)}\mathbb E_{\omega,v_i}\big[T^{\kappa_{e,\omega}(v_i)}_{e,\omega}(v_i)\big],$$
--   where $\kappa_{e,\omega}(v)$ is the set of seller reports at which the canonical first-best matching $M^*$ selects $e$ when buyer $i$ reports $v$.
--
--   Theorem 3.2 is the special case $T^\kappa_{e,\omega}(v)=\beta\,\mathbb E_{c_j}[(v-c_j)_+\mathbf 1\{c_j\in\kappa\}]$; the general form lets the bound depend on the edge and the cap.
--
--   **Formalization Note** $\ell^\kappa_{\alpha,e,\omega}$ is the typewise contribution (5) under the unconditioned seller prior; $V_\alpha(\mathcal I)$ uses the report domains.
--
--   Differences from the source:
--   - encoding: families z^κ_{e,ω} and targets T^κ_{e,ω} indexed by residual reports ω = θ_{−ij} → indexed by the edge and a full profile ω ∈ domainProfiles D; T e ω does not depend on the i- and j-coordinates of ω (hTres); z may, which changes nothing since z does not enter the conclusion; reason: a function of the residual profile is the same as a function of the full profile that ignores the two coordinates
--   - encoding: the report domains of Section 3.1 → D u with IsAuxDomain (finite nonempty or a bounded interval, carrying the prior), V_α(I) = ValphaOn I D α; reason: the published convention of base Theorem 3.2
--   - encoding: E_{ω,v_i}[T^{κ_{e,ω}(v_i)}_{e,ω}(v_i)] with finite expectations → ∫ over the product prior of θ ↦ T e θ (firstBestCap I rank e θ (θ_i) ∩ D_j) (θ_i), assumed integrable; reason: the integrand depends only on v_i and θ_{−ij}; finite expectation is integrability
--   - encoding: κ_{e,ω}(v), the first-best cap of the canonical M* → firstBestCap I rank e ω v ∩ D_j, for every tie order rank with IsTieOrder; reason: M* breaks ties by a fixed report-independent order; the statement holds for each such order
--   - encoding: ℓ^κ_{α,e,ω}(v) ≥ T^κ_{e,ω}(v) for every e, ω, κ, v; T^∅_{e,ω} = 0 → for every edge, domain profile ω, cap κ of D_j and buyer report v ∈ D_i (and T e ω ∅ v = 0 there), with ℓ the published typewise (eq. (5)); reason: the quantifier ranges of base Theorem 3.2
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem B.10, p.37 (pdf p.39); report domains and first-best caps §3.1, pp.8–9 (pdf pp.10–11)

import Mathlib
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_typewise
import Definitions.Def_BilatMatch_canonicalMax

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

/-- **Theorem B.10 (Composition with Cap-Dependent Bounds).** Liu, Qin, Wang, *From Bilateral Trade
to Matching Markets: Sharp Gains from Trade*, arXiv:2609.30702 (held version, sha256 ff1490ad…),
Theorem B.10, p.37 (pdf p.39); report domains and first-best caps of §3.1, pp.8–9.

Fix `α ≥ 0` and an independent matching market `I` with finitely many agents and downward-closed
feasibility, on report domains that are finite ordered sets or bounded intervals. For each edge `e`
and residual profile `ω`, let `z^κ_{e,ω}` be a cap-compatible family, and let `T^κ_{e,ω}(v)` be
typewise lower bounds with finite expectations and `T^∅_{e,ω} = 0`. If
`ℓ^κ_{α,e,ω}(v) ≥ T^κ_{e,ω}(v)` for every `e, ω, κ, v`, then
`V_α(I) ≥ ∑_{e=(i,j)} E_{ω,v_i}[T^{κ_{e,ω}(v_i)}_{e,ω}(v_i)]`, where `κ_{e,ω}(v)` is the first-best cap.

**Formalization Note**
* Report domains `D u` satisfy the published `IsAuxDomain`; `V_α(I)` is `ValphaOn I D α`.
* `z` and `T` are indexed by the edge and a full profile `ω ∈ domainProfiles D`. `T` does not depend on
  the `i`- and `j`-coordinates of `ω` (hypothesis `hTres`), so it is a function of the residual
  profile `θ_{−ij}` as in the paper; for `z` this makes no difference (the conclusion does not involve
  it).
* `κ_{e,ω}(v)` is the published `firstBestCap I rank e ω v` (the seller reports at which the canonical
  `M*` selects `e`) intersected with the seller domain; `rank` is any fixed report-independent tie
  order (`IsTieOrder`). The expectation is over the product prior of all types, of a function of
  `v_i` and `θ_{−ij}`; "finite expectations" is integrability of that function (`hTint`).
* `ℓ^κ_{α,e,ω}` is the published `typewise` (eq. (5)) with the unconditioned seller prior. The sum
  runs over the (finitely many) edges of `I`. -/
theorem theorem_B_10 (α : ℝ) (hα : 0 ≤ α) {B S : Type*} [Fintype B] [Fintype S]
    (I : Market B S) (hI : I.IsValid) (D : B ⊕ S → Set ℝ)
    (hD : ∀ u, IsAuxDomain (Sum.elim I.buyerLaw I.sellerLaw u) (D u))
    (rank : Set (B × S) → ℕ) (hrank : IsTieOrder I rank)
    (z : B × S → Profile B S → Set ℝ → ℝ → ℝ → ℝ)
    (hz : ∀ e ∈ I.edges, ∀ ω ∈ domainProfiles D,
      IsCapCompatible (D (Sum.inl e.1)) (D (Sum.inr e.2)) (z e ω))
    (T : B × S → Profile B S → Set ℝ → ℝ → ℝ)
    (hTres : ∀ e ∈ I.edges, ∀ ω ω' : Profile B S, (∀ i, i ≠ e.1 → ω.1 i = ω'.1 i) →
      (∀ j, j ≠ e.2 → ω.2 j = ω'.2 j) → T e ω = T e ω')
    (hT0 : ∀ e ∈ I.edges, ∀ ω ∈ domainProfiles D, ∀ v ∈ D (Sum.inl e.1), T e ω ∅ v = 0)
    (hTint : ∀ e ∈ I.edges, Integrable
      (fun θ : Profile B S => T e θ (firstBestCap I rank e θ (θ.1 e.1) ∩ D (Sum.inr e.2)) (θ.1 e.1))
      (typeMeasure I))
    (hbound : ∀ e ∈ I.edges, ∀ ω ∈ domainProfiles D, ∀ κ : Set ℝ, IsCap (D (Sum.inr e.2)) κ →
      ∀ v ∈ D (Sum.inl e.1),
        T e ω κ v ≤ typewise α (D (Sum.inl e.1)) (D (Sum.inr e.2)) (I.sellerLaw e.2) (z e ω κ) v) :
    ((∑ᶠ e ∈ I.edges, ∫ θ, T e θ (firstBestCap I rank e θ (θ.1 e.1) ∩ D (Sum.inr e.2)) (θ.1 e.1)
        ∂typeMeasure I : ℝ) : EReal) ≤ ValphaOn I D α := by sorry

end BilatMatch.Supplement
