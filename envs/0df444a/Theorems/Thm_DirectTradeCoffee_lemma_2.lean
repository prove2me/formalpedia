-- Prove2me | Theorems.Thm_DirectTradeCoffee_lemma_2
-- name    : DirectTradeCoffee.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:33.580992+00:00
-- url     : https://prove2.me/theorems/6a917b60-23d6-4072-bbad-01b1c175fb5c
-- title:
--   Lemma 2, p.12 — under uncertainty, $Q_L<Q_D<Q_H$
-- statement:
--   Suppose yield and/or blend price is uncertain at the time of contracting, that is, $\sigma_y^2>0$ or $\sigma_\varphi^2>0$. Then
--
--   $$
--   Q_L < Q_D < Q_H .
--   $$
--
--   Contracted acreage under the specialized (diversified) strategy is therefore more conservative (aggressive) than the optimal acreage of the deterministic model, and the three strategy classes are pairwise disjoint.
--
--   Differences from the source:
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - encoding: F has support Ω → F(Ωᶜ) = 0 and every open ball around a point of Ω has positive mass; reason: this is the definition of the support of a measure
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, Lemma 2, p.12; proof p.41

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

namespace DirectTradeCoffee

/-- **Lemma 2**, Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for Specialty Coffee*, MSOM
(2024), doi:10.1287/msom.2021.0586, p.12: if yield and/or blend price is uncertain at the time of
contracting (`σ_y² > 0` and/or `σ_φ² > 0`), then `Q_L < Q_D < Q_H`. -/
theorem lemma_2 (P : Params) (U : Uncertainty) (hσ : 0 < U.varY ∨ 0 < U.varφ) :
    QL P U < QD P U ∧ QD P U < QH P U := by sorry

end DirectTradeCoffee
