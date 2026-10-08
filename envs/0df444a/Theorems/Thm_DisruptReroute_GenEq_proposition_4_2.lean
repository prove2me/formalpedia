-- Prove2me | Theorems.Thm_DisruptReroute_GenEq_proposition_4_2
-- name    : DisruptReroute.GenEq.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:28.874976+00:00
-- url     : https://prove2.me/theorems/1af7af33-b13e-46ee-bb9b-18cc2358f138
-- title:
--   Proposition 4.2, p. 22 — unique partial switching-cost equilibrium
-- statement:
--   Fix a good $m$ and a feasible profile $\bar\sigma_i^m$ of unserved demands. Under the paper's market conditions and Assumption 4.2, a partial switched demand equilibrium exists. Every active buyer incurs the unique switching cost
--
--   $$\kappa_i^m=s_m^{-1}\left(\sum_{j:\,\bar\sigma_j^m>0}\bar\sigma_j^m\right),$$
--
--   and the corresponding efficient switched quantity equals the full unserved demand, $\sigma_i^m=\bar\sigma_i^m$.
--
--   The result identifies the strategic cost profile from the Nash condition of Definition 3.2. Uniqueness concerns active buyers; the p. 23 convention fixes costs outside that market.
--
--   **Formalization Note** A profile with no active buyers is allowed. The marginal-cost derivative in Assumption 4.2 is required only when the market is active, and differentiability at its total is explicit.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), p. 22, Proposition 4.2 and Assumption 4.2; proof E-Companion, EC pp. 9–11

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_Model

namespace DisruptReroute.GenEq

/-- Proposition 4.2. Uniqueness concerns the costs of active buyers. -/
theorem proposition_4_2 {N M : ℕ} (net : Network N M) (m : Fin M)
    (Δ : Matrix N M) (h : Standing net) (hΔ : InBounds net Δ)
    (hMC : MarginalCost net m (sbar net Δ m)) :
    ∃ cost : Fin N → ℝ,
      PartialS net m (sbar net Δ m) cost ∧
      (∀ i ∈ active N (sbar net Δ m), cost i = costStar net Δ m) ∧
      EfficientS net m (sbar net Δ m) cost (sbar net Δ m) ∧
      (∀ cost' : Fin N → ℝ, PartialS net m (sbar net Δ m) cost' →
        ∀ i ∈ active N (sbar net Δ m), cost' i = costStar net Δ m) := by sorry

end DisruptReroute.GenEq
