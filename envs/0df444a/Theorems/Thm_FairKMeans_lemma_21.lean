-- Prove2me | Theorems.Thm_FairKMeans_lemma_21
-- name    : FairKMeans.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:45.390483+00:00
-- url     : https://prove2.me/theorems/a5237626-f5ba-4ffc-8c9b-c957b5716bf2
-- title:
--   Lemma 21 — comparison bound $\mathrm{OPT}_\pi\le\mathrm{Cost}(\pi(T),S^\circ)\le C_T+\mathrm{Cost}^\circ+2C_e$
-- statement:
--   Let $(T,\phi_T)$ be a relaxed solution and $(S^\circ,\phi^\circ)$ a comparison solution with $|S^\circ|\le k$. Write $\pi(T)$ for the centroids with weights $w(t)$ and $\mathrm{OPT}_\pi=\min_{|S|\le k}\mathrm{Cost}(\pi(T),S)$. Then
--
--   $$\mathrm{OPT}_\pi\le\mathrm{Cost}(\pi(T),S^\circ)\le C_T+\mathrm{Cost}(P,S^\circ,\phi^\circ)+2C_e .$$
--
--   The alignment $C_e$ is the only term not controlled by the costs.
--
--   Differences from the source:
--   - encoding: OPT_π = min over |S| ≤ k → kmOpt, the infimum over families with 1 ≤ |S| ≤ k; reason: the empty family has cost +∞ and is never optimal
--   - encoding: C_e as the double sum of (32) → the second expression of (32); reason: equal because the rows of ϕ° sum to one
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 21, p.28 (PDF p.30); OPT_π, p.27 (PDF p.29); (32), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_Comparison

namespace FairKMeans

/-- **Lemma 21 (Comparison bound)**, p.28 (PDF 30). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held
version, sha256 73e9312c…).

For a relaxed solution `(T, φ_T)` and a comparison solution `(S°, φ°)` with `|S°| ≤ k`,
`OPT_π ≤ Cost(π(T), S°) ≤ C_T + Cost(P, S°, φ°) + 2C_e`, where
`OPT_π = min_{|S| ≤ k} Cost(π(T), S)` (p.27) and `π(T)` carries the weights `w(t)`. -/
theorem lemma_21 {d n m s s₀ : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ)
    (h : IsRelaxed I φ) (S₀ : Fin s₀ → E d) (φ₀ : Fin n → Fin s₀ → ℝ)
    (hc : IsComparison I S₀ φ₀) (hk : s₀ ≤ I.k) :
    kmOpt (cen I φ) (clusterWeight φ) I.k ≤ kmCost (cen I φ) (clusterWeight φ) S₀ ∧
      kmCost (cen I φ) (clusterWeight φ) S₀ ≤ CT I φ + cost I S₀ φ₀ + 2 * Ce I φ S₀ φ₀ := by sorry

end FairKMeans
