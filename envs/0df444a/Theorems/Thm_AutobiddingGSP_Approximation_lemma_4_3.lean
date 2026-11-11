-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_4_3
-- name    : AutobiddingGSP.Approximation.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:32.168915+00:00
-- url     : https://prove2.me/theorems/ff5cf8ef-275e-4f72-879a-6179a4287e90
-- title:
--   Lemma 4.3 — the quantile coupling has marginals ρ_2, …, ρ_T and support at most Q
-- statement:
--   Let $T\ge2$ and let $\rho_2,\dots,\rho_T$ be probability vectors. With $F_t$, $E_0\le\dots\le E_Q$, $w_h$, $u_h$ and $\sigma_h(t)=\min\{r:F_{t,r}\ge u_h\}$ as in §4.1, the weights $w_h$ ($h\in[Q]$) are nonnegative and sum to $1$, the mixture $\pi=\sum_{h\in[Q]}w_h\delta_{\sigma_h}$ is a probability distribution on insertion encodings, its insertion marginal at every step $t$ is $\rho_t$, and $\pi$ has at most $Q=\sum_{t=2}^T(t+1)-1$ support points.
--
--   Differences from the source:
--   - reading: weight w_h to σ_h for every h ∈ Q → h ∈ [Q] = {1, …, Q}; reason: Q is a number; p. 15 introduces w_h for h ∈ [Q] and the proof sums h = 1..Q (typo, INSIGHTS I1)
--   - reading: the first entry of F_t strictly greater than or equal to u_h → min{r : F_{t,r} ≥ u_h}, as displayed; reason: the display defines σ_h(t) with ≥
--   - generalization: ρ_2, …, ρ_T computed by the circuit → arbitrary probability vectors ρ_t; reason: the lemma's argument uses only that each ρ_t is a probability vector
--   - encoding: supported on at most Q = O(T²) deterministic allocations → |{σ : π(σ) ≠ 0}| ≤ Q with Q = ∑_{t=2}^T (t+1) − 1; reason: the explicit Q of p. 15, which is O(T²)
--   - encoding: steps 2..T → 0-based steps 1..T − 1; cumF ρ t 0 = F_{t,−1}; reason: Lean indexing
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 4.3, p. 15 (PDF 15)

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Insertion

namespace AutobiddingGSP.Approximation

/-- **Lemma 4.3 (Quantile Coupling)** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 15 (PDF 15)). Let `T ≥ 2` and let `ρ_2, …, ρ_T` be
probability vectors (`ρ_t` on the positions `0, …, t − 1`). With `F_t`, `E_0 ≤ ⋯ ≤ E_Q`,
`w_h = E_h − E_{h−1}`, `u_h = (E_{h−1} + E_h)/2` and `σ_h(t) = min{r : F_{t,r} ≥ u_h}`, the mixture
assigning weight `w_h` to `σ_h` for every `h ∈ [Q]` is a randomized allocation `π` (nonnegative
weights summing to one) whose insertion marginals are `ρ_2, …, ρ_T`, and `π` is supported on at most
`Q = ∑_{t=2}^{T} (t + 1) − 1 = O(T²)` deterministic allocations.

**Formalization Note** Steps are 0-based (Lean step `t` is the paper's `t + 1`); `ρ` at step
`0` is unused. The index set is `[Q] = {1, …, Q}` (the printed "`h ∈ Q`" is read as `h ∈ [Q]`). -/
theorem lemma_4_3 {T : ℕ} (hT : 2 ≤ T) (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ)
    (hρ : ∀ t : Fin T, 1 ≤ t.val → (∀ r, 0 ≤ ρ t r) ∧ ∑ r, ρ t r = 1) :
    (∀ h ∈ Finset.Icc 1 (couplingQ T), 0 ≤ weightW ρ h) ∧
    ∑ h ∈ Finset.Icc 1 (couplingQ T), weightW ρ h = 1 ∧
    (∀ σ, 0 ≤ quantileCoupling ρ σ) ∧ ∑ σ, quantileCoupling ρ σ = 1 ∧
    (∀ t : Fin T, 1 ≤ t.val → ∀ r, marginal (quantileCoupling ρ) t r = ρ t r) ∧
    (Finset.univ.filter (fun σ => quantileCoupling ρ σ ≠ 0)).card ≤ couplingQ T := by sorry

end AutobiddingGSP.Approximation
