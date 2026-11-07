-- Prove2me | Theorems.Thm_FairKMeans_lemma_22
-- name    : FairKMeans.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:54.728405+00:00
-- url     : https://prove2.me/theorems/35e882d8-13c0-41d6-b58b-4239c3d388a4
-- title:
--   Lemma 22 — stationarity bounds the alignment: $C_T+2\lambda C_\nu\le\mathrm{Cost}^\circ-2\lambda C_e+\tau$
-- statement:
--   Let $\rho\ge1$, $\lambda=\rho/(1+\rho)$ and $\tau\ge0$. Every $\tau$-stationary relaxed solution $(T,\phi_T)$ and every comparison solution $(S^\circ,\phi^\circ)$ satisfy
--
--   $$C_T+2\lambda C_\nu\le\mathrm{Cost}(P,S^\circ,\phi^\circ)-2\lambda C_e+\tau .$$
--
--   This is where the drift regularizer controls the alignment.
--
--   Differences from the source:
--   - encoding: C_e as the double sum of (32) → the second expression of (32); reason: equal because the rows of ϕ° sum to one
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 22, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_Comparison

namespace FairKMeans

/-- **Lemma 22 (Stationarity bound)**, p.29 (PDF 31). Cheng–Mo–Song–Ding, arXiv:2609.07974
(held version, sha256 73e9312c…).

Every τ-stationary relaxed solution `(T, φ_T)` (`τ ≥ 0`, Definition 9) and every comparison
solution `(S°, φ°)` satisfy `C_T + 2λC_ν ≤ Cost(P, S°, φ°) − 2λC_e + τ`. -/
theorem lemma_22 {d n m s s₀ : ℕ} (I : Instance d n m) (ρ : ℝ) (hρ : 1 ≤ ρ) (τ : ℝ)
    (hτ : 0 ≤ τ) (φ : Fin n → Fin s → ℝ) (h : IsRelaxed I φ) (hst : IsStationary I ρ τ φ)
    (S₀ : Fin s₀ → E d) (φ₀ : Fin n → Fin s₀ → ℝ) (hc : IsComparison I S₀ φ₀) :
    CT I φ + 2 * lam ρ * Cnu I φ ≤ cost I S₀ φ₀ - 2 * lam ρ * Ce I φ S₀ φ₀ + τ := by sorry

end FairKMeans
