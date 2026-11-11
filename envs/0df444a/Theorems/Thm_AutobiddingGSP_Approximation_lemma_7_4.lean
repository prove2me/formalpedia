-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_7_4
-- name    : AutobiddingGSP.Approximation.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:28:44.041604+00:00
-- url     : https://prove2.me/theorems/b3845feb-dcca-4fe1-9f9e-14dcc8dcc2b4
-- title:
--   Lemma 7.4 — the budget decoding (6) satisfies every gate
-- statement:
--   Fix $0\le\gamma<1$, $a=\lceil2/(1-\gamma)\rceil$, a well-formed Pure-Circuit instance with forward span at most five, and the auction of §7.1 built from it. For every γ-approximate ABE-B $(\alpha,\pi)$ of that auction, the assignment $x[v]=0$ if $\alpha_v\le c^{-1/3}$, $x[v]=1$ if $\alpha_v=1$, $x[v]=\bot$ otherwise, satisfies every gate.
--
--   Differences from the source:
--   - reading: the given Bounded-Forward-Span Pure-Circuit(5) instance → a PCInstance with WF (including outputs distinct from inputs) and FwdSpanLE 5; reason: the convention of §7.2 p. 33
--   - encoding: values c^{ℓ+θ} with c = a^36 → the integers a^{36ℓ+36θ}; c^{−1/3} = a^{−12}; reason: exact equal values
--   - encoding: bidder v ∈ V and the guard ⋆ → bidders 0..n−1 for the vertices, the guard last; a = paramA γ as a hypothesis a = ⌈2/(1−γ)⌉; reason: Lean indexing
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 7.4, p. 34 (PDF 34); construction §7.1 pp. 30–31

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Model
import Definitions.Def_AutobiddingGSP_Approximation_Search
import Definitions.Def_AutobiddingGSP_Approximation_PureCircuit
import Definitions.Def_AutobiddingGSP_Approximation_HardnessAuctions

namespace AutobiddingGSP.Approximation

/-- **Lemma 7.4** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 34 (PDF 34)). Fix `0 ≤ γ < 1`, `a = ⌈2/(1 − γ)⌉`, a
Bounded-Forward-Span Pure-Circuit(5) instance and the auction of §7.1 built from it. For every
γ-approximate ABE-B `(α, π)` of that auction, the assignment (6) — `x[v] = 0` if `α_v ≤ c^{−1/3}`,
`1` if `α_v = 1`, `⊥` otherwise — satisfies every gate of the instance. -/
theorem lemma_7_4 (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (a : ℕ) (ha : a = paramA γ)
    (C : PCInstance) (hC : C.WF) (hspan : C.FwdSpanLE 5)
    (α : Fin (budgetAuction a C).n → ℝ) (π : (budgetAuction a C).Alloc → ℝ)
    (heq : (budgetAuction a C).IsApproxABEB γ α π) :
    ∀ g ∈ C.gates, g.Sat (budgetDecode a ((budgetAuction a C).alphaAt α)) := by sorry

end AutobiddingGSP.Approximation
