-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_8_5
-- name    : AutobiddingGSP.Approximation.lemma_8_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:28:36.169011+00:00
-- url     : https://prove2.me/theorems/2714050e-87d6-42f6-852c-9d1d776aafbf
-- title:
--   Lemma 8.5 — a high ROI input bid forces α_v < a^24
-- statement:
--   In the setting of Lemma 8.4, for an occupied level $\ell$ with output bidder $v$: if some input bid at this level is at least $a^{68}c^\ell$, then $\alpha_v<a^{24}$ and $x[v]=0$.
--
--   Differences from the source:
--   - reading: the given Bounded-Forward-Span Pure-Circuit(5) instance → a PCInstance with WF (including outputs distinct from inputs) and FwdSpanLE 5; reason: the convention of §8.2 p. 39
--   - encoding: an occupied level ℓ and its output bidder v; input bids at this level → an entry (ℓ, v, inputs, θ) of roiLevels C; the input bid of u is α_u · a^θ c^ℓ with c = a^128; reason: the construction's level table, p. 36
--   - encoding: bidders v ∈ V and the two guards → bidders 0..n−1 for the vertices, guards last; a = paramA γ as a hypothesis a = ⌈2/(1−γ)⌉; reason: Lean indexing
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 8.5, p. 40 (PDF 40)

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_Search
import Definitions.Def_AutobiddingGSP_Approximation_PureCircuit
import Definitions.Def_AutobiddingGSP_Approximation_HardnessAuctions

namespace AutobiddingGSP.Approximation

/-- **Lemma 8.5 (A high input bid)** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 40 (PDF 40)). In the setting of Lemma 8.4, fix an
occupied level `ℓ`, and let `v` be its output bidder. If an input bid at this level is at least
`a^68 c^ℓ`, then `α_v < a^24`, and hence `x[v] = 0`.

**Formalization Note** The occupied level is an entry `(ℓ, v, inputs, θ)` of `roiLevels C`; the
input bid of an input bidder `u` is `α_u · a^θ c^ℓ`. -/
theorem lemma_8_5 (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (a : ℕ) (ha : a = paramA γ)
    (C : PCInstance) (hC : C.WF) (hspan : C.FwdSpanLE 5)
    (α : Fin (roiAuction a C).n → ℝ) (π : (roiAuction a C).Alloc → ℝ)
    (heq : (roiAuction a C).IsApproxABER γ α π)
    (e : ℕ × ℕ × List ℕ × ℕ) (he : e ∈ roiLevels C)
    (hhigh : ∃ u ∈ e.2.2.1, (a : ℝ) ^ 68 * ((a : ℝ) ^ 128) ^ e.1 ≤
      (roiAuction a C).alphaAt α u * ((a : ℝ) ^ e.2.2.2 * ((a : ℝ) ^ 128) ^ e.1)) :
    (roiAuction a C).alphaAt α e.2.1 < (a : ℝ) ^ 24 ∧
      roiDecode a ((roiAuction a C).alphaAt α) e.2.1 = Tri.zero := by sorry

end AutobiddingGSP.Approximation
