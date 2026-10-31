-- Prove2me | Theorems.Thm_FairDiffusionLimit_theorem_7_a
-- name    : FairDiffusionLimit.theorem_7_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:17.721025+00:00
-- url     : https://prove2.me/theorems/f3af6eeb-0ce9-48f9-b8f9-32f1c5785bfa
-- title:
--   Theorem 7(a) — uniform stability of the pre-limit fluid models (corrected: residual bound)
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   Suppose the deterministic DCP (38)–(43) is stable. Then there are a time $t_0>0$ and an index $k_0$ such that for every $k\ge k_0$, every solution $\hat w^k$ of the fluid model (55)–(59) of network $k$ with
--   $$|\hat w^k(0)|+|\bar u^k(1)|+|\bar v^k(1)|\le1$$
--   satisfies
--   $$\hat w^k(t)=0\qquad\text{for all } t\ge t_0. \tag{60}$$
--
--   The stability time $t_0$ is uniform in $k$; this is what makes the moment estimates of §4 (Lemma 10) uniform in the network index.
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). The fluid model uses the $k$-th network's $\rho^k_r$ in (59).
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
--   - reading: fluid model (55)–(59) with Λ̄_r(n) = ρ_r for n_r = 0 and the convention ŵ^k_r ≡ ν_r n̂^k_r (p.17) → IsFluidSol with the k-th network’s ρ^k_r in (59), n̂^k_r = ŵ^k_r/ν^k_r, and ŵ^k ≥ 0; reason: the fluid model of the k-th network, whose dynamics are (6)–(9) "with the index k suitably appended" (p.12); with ρ_r a class whose fluid workload is 0 is drained at rate ρ_r ≠ ρ^k_r and the model has no solution that stays nonnegative (L = R = 1, A = c = β = ν^k = 1, λ^k = 1 − 1/k: from ŵ(0) = 1/2 with zero residuals, ŵ decreases at slope −1 and cannot continue at 0); as k → ∞ the two agree
--   - correction: "any solution ŵ^k(t) to the fluid model in (55-58) with |ŵ^k(0)| ≤ 1" → solutions with |ŵ^k(0)| + |ū^k(1)| + |v̄^k(1)| ≤ 1; reason: as printed (60) is false: L = R = 1, A = c = β = ν^k = 1, λ^k = 1 − 1/k (θ = −1 < 0, so the DCP is stable by Theorem 8(a)); ŵ^k(0) = 1/2, ū^k(1) = 0, v̄^k(1) = kT, d̄^k(t) = t until ŵ^k reaches 0 at t* = 1/2 + kT (afterwards d̄^k grows at rate ρ^k and ŵ^k stays 0) solves (55)–(59), with ŵ^k(t) = 1/2 + k·min(t, T) − t > 0 on [0, T] for every T; the bound is Lemma 6’s hypothesis, through which the proof reaches (60)
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Theorem 7(a), p.18 (PDF 18)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Theorem 7(a)** (uniform stability; Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 18), corrected: if the deterministic DCP
(38)–(43) is stable, there is a time `t₀ > 0` such that for all sufficiently large `k`, every solution
`ŵ^k` of the fluid model (55)–(58) with `|ŵ^k(0)| + |ū^k(1)| + |v̄^k(1)| ≤ 1` satisfies `ŵ^k(t) = 0`
for `t ≥ t₀` (60).

**Formalization Note.** The page bounds only `|ŵ^k(0)| ≤ 1`; then (60) fails (a large residual work
`v̄^k(1)` keeps `ŵ^k` positive for an arbitrarily long time), so the hypothesis of Lemma 6 is used.
The fluid model uses `ρ^k_r` in (59) (see `IsFluidSol`). -/
theorem theorem_7_a {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H)
    (hDS : S.DetStable H) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ (ub vb : Fin R → ℝ) (w d : ℝ → Fin R → ℝ) (y : ℝ → Fin L → ℝ) (z : ℝ → Fin (R - L) → ℝ),
        S.IsFluidSol H k ub vb w d y z → l1 (w 0) + l1 ub + l1 vb ≤ 1 →
        ∀ t : ℝ, t0 ≤ t → w t = 0 := by sorry

end FairDiffusionLimit
