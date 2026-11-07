-- Prove2me | Theorems.Thm_FairKMeans_lemma_23
-- name    : FairKMeans.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:40.943206+00:00
-- url     : https://prove2.me/theorems/bacffb37-f62b-4af5-aa89-b7d896695df5
-- title:
--   Lemma 23 — cost of the final solution $\le(2\rho+1)\mathrm{Cost}^\circ-2\rho C_\nu+(1+\rho)\tau$
-- statement:
--   Let $\rho\ge1$, $\tau\ge0$, let $(T,\phi_T)$ be a $\tau$-stationary relaxed solution and $(S^\circ,\phi^\circ)$ a comparison solution with $|S^\circ|\le k$. Then
--
--   $$C_T+\rho\,\mathrm{OPT}_\pi\le(2\rho+1)\mathrm{Cost}(P,S^\circ,\phi^\circ)-2\rho\,C_\nu+(1+\rho)\tau. \tag{33}$$
--
--   Moreover, if $S_\pi$ is a family of at least one and at most $k$ centers with $\mathrm{Cost}(\pi(T),S_\pi)\le\rho\,\mathrm{OPT}_\pi$ (the output of a $\rho$-approximate weighted $k$-means algorithm on $\pi(T)$), then every optimal fair assignment $\phi^*_{S_\pi}$ to $S_\pi$ satisfies
--
--   $$\mathrm{Cost}(P,S_\pi,\phi^*_{S_\pi})\le(2\rho+1)\mathrm{Cost}(P,S^\circ,\phi^\circ)-2\rho\,C_\nu+(1+\rho)\tau. \tag{34}$$
--
--   This is the main inequality of the analysis.
--
--   Differences from the source:
--   - encoding: S_π the center set the ρ-approximate algorithm returns on π(T) → every family with 1 ≤ |S_π| ≤ k and Cost(π(T), S_π) ≤ ρ OPT_π; reason: this is exactly the algorithm's guarantee (p.20)
--   - reading: the optimal fair assignment ϕ*_{S_π} → every optimal fair assignment; reason: the LP may have several optima; the proof applies to each
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 23, (33)–(34), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_Comparison

namespace FairKMeans

/-- **Lemma 23 (Cost of the final solution)**, p.29 (PDF 31), (33)–(34). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

If `(T, φ_T)` is τ-stationary and `(S°, φ°)` is a comparison solution with `|S°| ≤ k`, then
`C_T + ρ OPT_π ≤ (2ρ+1)Cost(P, S°, φ°) − 2ρC_ν + (1+ρ)τ` (33). Moreover, for a center set `S_π`
returned by a ρ-approximate weighted k-means algorithm on `π(T)` (at least one and at most `k`
centers, `Cost(π(T), S_π) ≤ ρ OPT_π`), every optimal fair assignment `φ*_{S_π}` to `S_π`
satisfies `Cost(P, S_π, φ*_{S_π}) ≤ (2ρ+1)Cost(P, S°, φ°) − 2ρC_ν + (1+ρ)τ` (34). -/
theorem lemma_23 {d n m s s₀ : ℕ} (I : Instance d n m) (ρ : ℝ) (hρ : 1 ≤ ρ) (τ : ℝ)
    (hτ : 0 ≤ τ) (φ : Fin n → Fin s → ℝ) (h : IsRelaxed I φ) (hst : IsStationary I ρ τ φ)
    (S₀ : Fin s₀ → E d) (φ₀ : Fin n → Fin s₀ → ℝ) (hc : IsComparison I S₀ φ₀)
    (hk : s₀ ≤ I.k) :
    CT I φ + ρ * kmOpt (cen I φ) (clusterWeight φ) I.k ≤
        (2 * ρ + 1) * cost I S₀ φ₀ - 2 * ρ * Cnu I φ + (1 + ρ) * τ ∧
      ∀ (sπ : ℕ) (Sπ : Fin sπ → E d), 1 ≤ sπ → sπ ≤ I.k →
        kmCost (cen I φ) (clusterWeight φ) Sπ ≤ ρ * kmOpt (cen I φ) (clusterWeight φ) I.k →
        ∀ ψ : Fin n → Fin sπ → ℝ, IsOptFairAssign I Sπ ψ →
          cost I Sπ ψ ≤ (2 * ρ + 1) * cost I S₀ φ₀ - 2 * ρ * Cnu I φ + (1 + ρ) * τ := by sorry

end FairKMeans
