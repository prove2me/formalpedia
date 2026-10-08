-- Prove2me | Theorems.Thm_DataDrivenRO_KS_theorem_EC_2
-- name    : DataDrivenRO.KS.theorem_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:44:51.038577+00:00
-- url     : https://prove2.me/theorems/6000b355-2417-4c60-b0b3-cc5dd4cf5d60
-- title:
--   Theorem EC.2, p. ec3 — for monotone g, sup over 𝒫^{KS}_i of E[g(ũᵢ)] is max(Σⱼ q^L_j g(û^(j)_i), Σⱼ q^R_j g(û^(j)_i))
-- statement:
--   In the setting of §5.1 (with $N\ge1$, $0<\Gamma<1$ and $\hat u^{(0)}_i<\dots<\hat u^{(N+1)}_i$), fix a coordinate $i$ and let $g:\mathbb R\to\mathbb R$ be monotone (non-decreasing or non-increasing). Then
--   $$\sup_{\mathbb P_i\in\mathcal P^{KS}_i}\mathbb E^{\mathbb P_i}[g(\tilde u_i)]=\max\Big(\sum_{j=0}^{N+1}q^L_j(\Gamma)g(\hat u^{(j)}_i),\ \sum_{j=0}^{N+1}q^R_j(\Gamma)g(\hat u^{(j)}_i)\Big),$$
--   i.e. the right-hand side is the least upper bound of the expectations of $g$ over the KS region.
--
--   Although $\mathcal P^{KS}_i$ is infinite dimensional, the worst case of a monotone expectation over it is attained at one of the two boundary distributions of the KS band. This evaluates the inner supremum of (16).
--
--   **Formalization Note** The supremum is stated as `IsLUB` of the set of integrals. Each measure of the region is a probability measure carried by the compact box, and a monotone $g$ is measurable and bounded there, so every integral is a genuine expectation. The points $\hat u^{(j)}_i$ are ordered (`Monotone (uhat i)`), ties allowed: they are the box ends and the order statistics of the sample.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem EC.2, (EC.3), p. ec3

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem theorem_EC_2 {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d)
    (g : ℝ → ℝ) (hg : Monotone g ∨ Antitone g) :
    IsLUB ((fun Q : Measure ℝ => ∫ x, g x ∂Q) '' ksRegion uhat Γ i)
      (max (∑ j, qL N Γ j * g (uhat i j)) (∑ j, qR N Γ j * g (uhat i j))) := by sorry

end DataDrivenRO.KS
