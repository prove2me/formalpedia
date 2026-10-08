-- Prove2me | Theorems.Thm_DisruptReroute_GenEq_lemma_A_7
-- name    : DisruptReroute.GenEq.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:44.183256+00:00
-- url     : https://prove2.me/theorems/d92b5fd8-edd2-4783-bcbf-39935bdeeed5
-- title:
--   Lemma A.7, EC p. 11 — ex-post net worth decreases with disruption
-- statement:
--   Let $(\Gamma^A,\Delta^A)$ and $(\Gamma^B,\Delta^B)$ be two feasible profiles of undelivered orders and unserved demands in the same network. If every coordinate of $\Gamma^A$ and $\Delta^A$ is at most the corresponding coordinate of $\Gamma^B$ and $\Delta^B$, then every firm's ex-post net worth under partial equilibrium satisfies
--
--   $$e_i^*(\Gamma^A,\Delta^A)\ge e_i^*(\Gamma^B,\Delta^B).$$
--
--   This monotonicity connects additional failed deliveries to weaker firm balance sheets and is used to compare successive cascade states.
--
--   **Formalization Note** The profiles lie in the order box $[0,O]$. The inverse market prices use aggregate undelivered orders and aggregate unserved demand, as in (18). The proof printed below Lemma A.7 has single-firm inverse arguments and omitted firm indices; the statement uses the main-text convention.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), E-Companion, p. EC 11 (PDF p. 53), Lemma A.7; main text pp. 17, 22–23, (10), (18)

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_Model

namespace DisruptReroute.GenEq

/-- Lemma A.7, for feasible undelivered-order and unserved-demand profiles. -/
theorem lemma_A_7 {N M : ℕ} (net : Network N M)
    (ΓA ΓB ΔA ΔB : Matrix N M)
    (h : Standing net)
    (hΓA : InBounds net ΓA) (hΓB : InBounds net ΓB)
    (hΔA : InBounds net ΔA) (hΔB : InBounds net ΔB)
    (hΓ : ΓA ≤ ΓB) (hΔ : ΔA ≤ ΔB) :
    ∀ i : Fin N, eStar net ΓB ΔB i ≤ eStar net ΓA ΔA i := by sorry

end DisruptReroute.GenEq
