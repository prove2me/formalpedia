-- Prove2me | Theorems.Thm_DataDrivenRO_KS_qL_qR_mem_ksRegion
-- name    : DataDrivenRO.KS.qL_qR_mem_ksRegion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:44:43.540004+00:00
-- url     : https://prove2.me/theorems/021649a6-4c7c-45f4-9204-a0e67f093e50
-- title:
--   Proof of Theorem EC.2, p. ec3 — the discrete laws with masses q^L(Γ), q^R(Γ) on û^(0)_i,…,û^(N+1)_i lie in 𝒫^{KS}_i
-- statement:
--   In the setting of §5.1 (with $N\ge1$, $0<\Gamma<1$ and $\hat u^{(0)}_i<\hat u^{(1)}_i<\dots<\hat u^{(N+1)}_i$), fix a coordinate $i$. The discrete distributions
--   $$\sum_{j=0}^{N+1}q^L_j(\Gamma)\,\delta_{\hat u^{(j)}_i}\qquad\text{and}\qquad\sum_{j=0}^{N+1}q^R_j(\Gamma)\,\delta_{\hat u^{(j)}_i}$$
--   both belong to the Kolmogorov–Smirnov confidence region $\mathcal P^{KS}_i$.
--
--   These two laws are the left-hand and right-hand boundaries of the KS band; their membership gives the "$\ge$" half of Theorem EC.2.
--
--   **Formalization Note** The points are ordered, $\hat u^{(0)}_i\le\hat u^{(1)}_i\le\dots\le\hat u^{(N+1)}_i$ (`Monotone (uhat i)`): the order statistics of the sample, which lies in the box. Ties are allowed, as on the page.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem EC.2, first sentence, p. ec3

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem qL_qR_mem_ksRegion {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d) :
    lawOn (uhat i) (qL N Γ) ∈ ksRegion uhat Γ i ∧ lawOn (uhat i) (qR N Γ) ∈ ksRegion uhat Γ i := by sorry

end DataDrivenRO.KS
