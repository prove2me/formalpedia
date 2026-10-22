-- Prove2me | Theorems.Thm_EJASpectral_RootDet_eq_109c_nonneg
-- name    : EJASpectral.RootDet.eq_109c_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:20.531444+00:00
-- url     : https://prove2.me/theorems/fe5f4740-7513-4663-abf7-09d325f33fd9
-- title:
--   (109c), p. 25 — d⁻¹φ Σᵢ δᵢ²(‖σ‖ − m₁ + 2(‖σ‖ − σᵢ)) ≥ 0 for every σ ∈ ℝ^d
-- statement:
--   Let $d\ge1$, $\sigma\in\mathbb R^d$ and $\varphi>0$. Write $m_1 := d^{-1}\sum_i\sigma_i$ for the mean, $\delta_i := \sigma_i - m_1$, and $\|\sigma\| := \big(\sum_i\sigma_i^2\big)^{1/2}$ for the Euclidean norm. Then
--   $$d^{-1}\varphi\sum_{i\in[\![d]\!]}\delta_i^2\big(\|\sigma\| - m_1 + 2(\|\sigma\| - \sigma_i)\big) \ge 0. \tag{109c}$$
--
--   This scalar inequality is the final step of the proof of Proposition 7.1: by (105), (107) and (108), the compatibility condition (103) is equivalent to the nonnegativity of (109c).
--
--   **Formalization Note** $\|\sigma\|$ is the Euclidean norm, written $\sqrt{\sum_i\sigma_i^2}$ (not Lean's default sup norm on $\mathbb R^d$). In the paper $\varphi = \varphi(w)>0$; here it is any positive real.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 25, proof of Proposition 7.1, (109c) and the two sentences after it

import Mathlib

namespace EJASpectral.RootDet

/-- (109c), p. 25: for `σ ∈ ℝ^d`, `φ > 0`, `m₁ = d⁻¹ Σᵢ σᵢ`, `δᵢ = σᵢ − m₁` and the
Euclidean norm `‖σ‖ = (Σᵢ σᵢ²)^{1/2}`, the quantity `d⁻¹ φ Σᵢ δᵢ² (‖σ‖ − m₁ + 2(‖σ‖ − σᵢ))` is
nonnegative. -/
theorem eq_109c_nonneg {d : ℕ} (hd : 0 < d) (σ : Fin d → ℝ) (φ : ℝ) (hφ : 0 < φ) :
    0 ≤ ((d : ℝ))⁻¹ * φ *
      ∑ i, (σ i - ((d : ℝ))⁻¹ * ∑ j, σ j) ^ 2 *
        (Real.sqrt (∑ j, σ j ^ 2) - ((d : ℝ))⁻¹ * ∑ j, σ j +
          2 * (Real.sqrt (∑ j, σ j ^ 2) - σ i)) := by sorry

end EJASpectral.RootDet
