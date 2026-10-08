-- Prove2me | Theorems.Thm_DisruptReroute_GenEq_proposition_4_1
-- name    : DisruptReroute.GenEq.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:32.37433+00:00
-- url     : https://prove2.me/theorems/a58fda26-f98a-45eb-ad05-2d1047a0ad60
-- title:
--   Proposition 4.1, p. 22 — unique partial rerouting-price equilibrium
-- statement:
--   Fix a good $m$ and a feasible profile $\bar r_i^m$ of undelivered orders. Under the paper's market conditions and Assumption 4.1, a partial rerouted supply equilibrium exists. Every active seller charges the unique market price
--
--   $$\pi_i^m=d_m^{-1}\left(\sum_{j:\,\bar r_j^m>0}\bar r_j^m\right),$$
--
--   and the corresponding efficient rerouted quantity equals the full undelivered order, $r_i^m=\bar r_i^m$.
--
--   The result identifies the strategic price profile from the Nash condition of Definition 3.1. Uniqueness concerns active sellers; prices of firms outside this market are economically immaterial until the paper's p. 23 convention fixes them.
--
--   **Formalization Note** A profile with no active sellers is allowed. The marginal-revenue derivative in Assumption 4.1 is required only when the market is active, and differentiability at its total is explicit.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), p. 22, Proposition 4.1 and p. 21, Assumption 4.1; proof E-Companion, EC pp. 5–6

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_Model

namespace DisruptReroute.GenEq

/-- Proposition 4.1. Uniqueness concerns the prices of active sellers;
    prices outside that market are immaterial until the p. 23 convention. -/
theorem proposition_4_1 {N M : ℕ} (net : Network N M) (m : Fin M)
    (Γ : Matrix N M) (h : Standing net) (hΓ : InBounds net Γ)
    (hMR : MarginalRevenue net m (rbar Γ m)) :
    ∃ price : Fin N → ℝ,
      PartialR net m (rbar Γ m) price ∧
      (∀ i ∈ active N (rbar Γ m), price i = priceStar net Γ m) ∧
      EfficientR net m (rbar Γ m) price (rbar Γ m) ∧
      (∀ price' : Fin N → ℝ, PartialR net m (rbar Γ m) price' →
        ∀ i ∈ active N (rbar Γ m), price' i = priceStar net Γ m) := by sorry

end DisruptReroute.GenEq
