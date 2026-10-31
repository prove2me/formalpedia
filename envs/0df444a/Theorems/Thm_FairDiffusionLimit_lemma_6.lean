-- Prove2me | Theorems.Thm_FairDiffusionLimit_lemma_6
-- name    : FairDiffusionLimit.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:07.281421+00:00
-- url     : https://prove2.me/theorems/f843ad25-35ff-49f9-8a77-f9a841a46944
-- title:
--   Lemma 6 — the shifted pre-limit fluid models have deterministic-DCP limits along subsequences
-- statement:
--   Let $(A,c,\beta,F^a,F^s,\lambda^k,\nu^k,\lambda,\nu,\theta,p)$ be a sequence of resource-sharing networks satisfying the standing assumptions of §2 (including (10)–(15)) and the heavy-traffic condition $A\rho=c$ (11), and let $H$ satisfy (17).
--
--   There is a constant $\kappa_w$, depending only on the network parameters, with the following property. For each $k\ge1$ let $(\hat w^k,\bar d^k,\hat y^k,\hat z^k)$ with residual parameters $\bar u^k(1),\bar v^k(1)$ solve the fluid model (55)–(59) of network $k$, with
--   $$|\hat w^k(0)+\bar u^k(1)+\bar v^k(1)|\le1 .$$
--   Let $t^k_0\to0$ with $kt^k_0\to\infty$. Then every subsequence of $k$ has a further subsequence $\mathcal K$ and a solution $\hat w$ of the deterministic DCP (38)–(43) with $|\hat w(0)|\le\kappa_w$ such that
--   $$\hat w^k(t^k_0+t)\to\hat w(t)\quad\text{uniformly on compact subsets of } t\ge0,\ k\to\infty \text{ along }\mathcal K.$$
--
--   This lemma transfers the stability of the deterministic DCP to the pre-limit fluid models (Theorem 7(a)).
--
--   **Formalization Note** $|\cdot|$ is the $\ell^1$ norm. Networks are indexed by $k\in\mathbb N$ (index $0$ is a dummy network). The fluid model uses the $k$-th network's $\rho^k_r$ in (59) (see the Differences).
--
--   Differences from the source:
--   - encoding: |·| (absolute value of the sum of components; p.43) → ℓ¹ norm l1 x = ∑ᵢ |xᵢ| (stNorm on 𝒳 = ℝ^{3R}); reason: the two agree on the nonnegative vectors where the paper applies |·|
--   - encoding: networks k = 1, 2, …; "for sufficiently large k" → k : ℕ with a dummy network 0 (λ⁰, ν⁰ > 0 only); "sufficiently large k" as ∃ k₀, ∀ k ≥ k₀ or ∀ᶠ k in atTop; reason: network 0 enters no statement except through limits or k ≥ k₀; any paper sequence extends by λ⁰ = λ¹, ν⁰ = ν¹
--   - encoding: A ≥ 0 of full row rank L (p.8); Λ(n) "is the solution" of (3) → also every column of A has a positive entry; reason: without it Γ is unbounded in γ_r, (3) has no solution and the paper’s Λ(n) is undefined; it excludes only undefined cases
--   - encoding: "Define an R × (R − L) matrix H: ABH = 0 and HᵀBH = I" (17) → H : Matrix (Fin R) (Fin (R − L)) ℝ a parameter satisfying (17); reason: (17) does not determine H; the statements hold for every such H
--   - encoding: DCP (27)–(32) / (38)–(43) with ∫ wᵀG dy = 0 → continuous paths on [0, ∞); (30)/(41) as "y_ℓ is constant on every [s, t] on which (Gᵀw)_ℓ > 0"; reason: the DCP is posed for continuous processes (p.12–13); for continuous w with Gᵀw ≥ 0 and nondecreasing y the two forms of (30) are equivalent
--   - reading: fluid model (55)–(59) with Λ̄_r(n) = ρ_r for n_r = 0 and the convention ŵ^k_r ≡ ν_r n̂^k_r (p.17) → IsFluidSol with the k-th network’s ρ^k_r in (59), n̂^k_r = ŵ^k_r/ν^k_r, and ŵ^k ≥ 0; reason: the fluid model of the k-th network, whose dynamics are (6)–(9) "with the index k suitably appended" (p.12); with ρ_r a class whose fluid workload is 0 is drained at rate ρ_r ≠ ρ^k_r and the model has no solution that stays nonnegative (L = R = 1, A = c = β = ν^k = 1, λ^k = 1 − 1/k: from ŵ(0) = 1/2 with zero residuals, ŵ decreases at slope −1 and cannot continue at 0); as k → ∞ the two agree
--   - encoding: "for any subsequence of k, there exists a further subsequence 𝒦" → φ strictly increasing, ∃ ψ strictly increasing, 𝒦 = φ ∘ ψ; reason: the same subsequences
--   - encoding: "κ_w is a constant that depends only on network parameters" → ∃ κ_w placed after the network data and before every sequence, subsequence and initial law; reason: depending only on the network parameters is exactly this quantifier position
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), Lemma 6, p.18 (PDF 18)

import Mathlib
import Definitions.Def_FairDiffusionLimit_DCP

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- **Lemma 6** (Ye–Yao, *Diffusion limit of fair resource control — stationarity and interchange of limits*, SSRN 2579541 (2015), p. 18): there is a constant `κ_w` (depending only on the network
parameters) such that, for every sequence of solutions `ŵ^k` of the fluid models (55)–(58) with
`|ŵ^k(0) + ū^k(1) + v̄^k(1)| ≤ 1`, every sequence of times `t^k_0 → 0` with `k t^k_0 → ∞`, and every
subsequence of `k`, there are a further subsequence `𝒦` and a solution `ŵ` of the deterministic DCP
(38)–(43) with `|ŵ(0)| ≤ κ_w` such that `ŵ^k(t^k_0 + t) → ŵ(t)` u.o.c. in `t ≥ 0` along `𝒦`.

**Formalization Note.** Subsequences are `φ ∘ ψ` with `φ, ψ` strictly increasing; u.o.c. convergence
is the published `Reiman84.QueueLength.UocTendsto`. The fluid model is `IsFluidSol` (with `ρ^k_r` in
(59)). -/
theorem lemma_6 {L R : ℕ} (S : NetSeq L R) (hS : S.Standing) (hHT : S.HeavyTraffic)
    (H : Matrix (Fin R) (Fin (R - L)) ℝ) (hH : S.IsH H) :
    ∃ κw : ℝ, ∀ (ub vb : ℕ → Fin R → ℝ) (w d : ℕ → ℝ → Fin R → ℝ) (y : ℕ → ℝ → Fin L → ℝ)
      (z : ℕ → ℝ → Fin (R - L) → ℝ),
      (∀ k : ℕ, 1 ≤ k → S.IsFluidSol H k (ub k) (vb k) (w k) (d k) (y k) (z k)) →
      (∀ k : ℕ, 1 ≤ k → l1 (w k 0 + ub k + vb k) ≤ 1) →
      ∀ t0 : ℕ → ℝ, Tendsto t0 atTop (𝓝 0) → Tendsto (fun k : ℕ => (k : ℝ) * t0 k) atTop atTop →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ (wl : ℝ → Fin R → ℝ) (yl : ℝ → Fin L → ℝ) (zl : ℝ → Fin (R - L) → ℝ),
          S.IsDCPSol H (fun t => t • S.θ) wl yl zl ∧ l1 (wl 0) ≤ κw ∧
          Reiman84.QueueLength.UocTendsto (fun n t => w (φ (ψ n)) (t0 (φ (ψ n)) + t)) wl := by sorry

end FairDiffusionLimit
