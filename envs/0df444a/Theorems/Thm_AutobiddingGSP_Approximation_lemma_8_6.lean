-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_8_6
-- name    : AutobiddingGSP.Approximation.lemma_8_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:28:57.218201+00:00
-- url     : https://prove2.me/theorems/cf96a4b4-7e89-4c43-83f0-f51daba5e2b4
-- title:
--   Lemma 8.6 — the ROI decoding (9) satisfies every gate
-- statement:
--   Fix $0\le\gamma<1$, $a=\lceil2/(1-\gamma)\rceil$, a well-formed Pure-Circuit instance with forward span at most five, and the auction of §8.1 built from it. For every γ-approximate ABE-R $(\alpha,\pi)$ of that auction, the assignment $x[v]=0$ if $\alpha_v\le a^{24}$, $x[v]=1$ if $\alpha_v\ge a^{64}$, $x[v]=\bot$ otherwise, satisfies every gate.
--
--   Differences from the source:
--   - reading: the given Bounded-Forward-Span Pure-Circuit(5) instance → a PCInstance with WF (including outputs distinct from inputs) and FwdSpanLE 5; reason: the convention of §8.2 p. 39
--   - encoding: bidders v ∈ V and the two guards → bidders 0..n−1 for the vertices, guards last; a = paramA γ as a hypothesis a = ⌈2/(1−γ)⌉; reason: Lean indexing
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 8.6, p. 40 (PDF 40); proof p. 41

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_Search
import Definitions.Def_AutobiddingGSP_Approximation_PureCircuit
import Definitions.Def_AutobiddingGSP_Approximation_HardnessAuctions

namespace AutobiddingGSP.Approximation

/-- **Lemma 8.6** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 40 (PDF 40)). Fix `0 ≤ γ < 1`, `a = ⌈2/(1 − γ)⌉`, a
Bounded-Forward-Span Pure-Circuit(5) instance and the auction of §8.1 built from it. For every
γ-approximate ABE-R `(α, π)` of that auction, the assignment (9) — `x[v] = 0` if `α_v ≤ a^24`,
`1` if `α_v ≥ a^64`, `⊥` otherwise — satisfies every gate of the instance. -/
theorem lemma_8_6 (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (a : ℕ) (ha : a = paramA γ)
    (C : PCInstance) (hC : C.WF) (hspan : C.FwdSpanLE 5)
    (α : Fin (roiAuction a C).n → ℝ) (π : (roiAuction a C).Alloc → ℝ)
    (heq : (roiAuction a C).IsApproxABER γ α π) :
    ∀ g ∈ C.gates, g.Sat (roiDecode a ((roiAuction a C).alphaAt α)) := by sorry

end AutobiddingGSP.Approximation
