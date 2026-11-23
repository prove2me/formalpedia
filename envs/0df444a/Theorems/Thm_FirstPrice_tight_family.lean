-- Prove2me | Theorems.Thm_FirstPrice_tight_family
-- name    : FirstPrice.tight_family
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:27.39887+00:00
-- url     : https://prove2.me/theorems/eadaa5f1-ae84-4096-abd5-84eca7771d11
-- title:
--   Jin–Lu Example 4 and Lemmas 6.1–6.2 — sharp finite-bidder equilibrium family
-- statement:
--   There is a sequence of finite independent-private-value first-price auction instances, each with an exact mixed Bayes–Nash equilibrium and an admissible highest-bid tie rule, with all values in $[0,1]$, such that
--   $$
--   \mathbb E[v_k^\star]\longrightarrow1,
--   \qquad
--   \mathbb E[v_k^{\mathrm{eq}}]\longrightarrow1-e^{-2}.
--   $$
--   The equilibria use nonnegative bids no larger than value, hence bids in $[0,1]$. Each instance has finitely many bidders. This packages Jin–Lu's Example 4 and the welfare limits of their Lemmas 6.1 and 6.2; the explicit value laws, bid kernels, and tie priorities are part of the construction to be supplied by a proof, rather than new axiomatic input.
--
--   This is the tightness dependency for `ProcurementPoA.DeterministicCap.Supplement.remark_4_2`. The affine map $c=U-(U-L)v$ converts it to procurement, and `ProcurementPoA.DeterministicCap.Supplement.tight_ratio_limit` gives the resulting limiting cost ratio.
--
--   **Formalization Note** The bidder count is allowed to vary with $k$, as in the source. Real-valued limits of the extended-nonnegative-real welfare expectations are used; bounded values in $[0,1]$ ensure these are the ordinary finite expectations.
-- source:
--   Y. Jin and P. Lu, First Price Auction is 1-1/e^2 Efficient, J. ACM 70(5), 2023, Example 4 in Section 6 and Lemmas 6.1–6.2, https://doi.org/10.1145/3617902 and https://arxiv.org/abs/2207.01761; as rescaled and invoked by Palazzotto–Cristi, STOC 2027 submission 293, Remark 4.2, p. 9 (printed p. 7).

import Mathlib
import Definitions.Def_FirstPrice_ValueAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

theorem FirstPrice.tight_family :
    ∃ (N : ℕ → ℕ) (D : ∀ k, ProcurementPoA.DeterministicCap.IndependentTypes (N k))
      (τ : ∀ k, ProcurementPoA.DeterministicCap.TieRule (N k))
      (σ : ∀ k, ProcurementPoA.DeterministicCap.MixedProfile (N k)),
      (∀ k, ∀ i, (D k).types i ⊆ Set.Icc 0 1) ∧
      (∀ k, IsBNE (D k) (τ k) (σ k)) ∧
      Filter.Tendsto (fun k => (optimalWelfare (D k)).toReal) Filter.atTop (𝓝 1) ∧
      Filter.Tendsto (fun k => (welfare (D k) (τ k) (σ k)).toReal) Filter.atTop
        (𝓝 (1 - ProcurementPoA.DeterministicCap.epsilon)) := by sorry
