-- Prove2me | Theorems.Thm_AdBlocking_Surplus_sign_criterion
-- name    : AdBlocking.Surplus.sign_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:17.43028+00:00
-- url     : https://prove2.me/theorems/10c23ef4-40c7-4617-b0d5-6db9c78c62c5
-- title:
--   Proof of Proposition 3 — sign criterion for surplus
-- statement:
--   Let $a,G,C_0,C_\Delta$ be positive and set $q(\bar\kappa)=[a+G/\bar\kappa]^{-1}$ and $h(\bar\kappa)=q(\bar\kappa)C_0+q(\bar\kappa)^2C_\Delta/\bar\kappa$. Then $h$ converges to $C_0/a$. If $C_\Delta\le C_0G$, $h$ is strictly increasing and remains below that limit. If $C_\Delta>C_0G$, $h$ increases up to one positive threshold, then decreases, and lies above the limit for all sufficiently large $\bar\kappa$:
--
--   $$\operatorname{sgn}\bigl(h(\bar\kappa)-C_0/a\bigr)\text{ for large }\bar\kappa
--     =\operatorname{sgn}(C_\Delta-C_0G).$$
--
--   This algebraic criterion is the comparison step used in the proof of Proposition 3.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 44 (PDF 45), proof of Proposition 3, paragraph after equation (11)

import Mathlib

open Filter Topology

namespace AdBlocking.Surplus

theorem sign_criterion
    (a G C₀ CΔ : ℝ) (ha : 0 < a) (hG : 0 < G) (hC₀ : 0 < C₀) (hCΔ : 0 < CΔ) :
    let h : ℝ → ℝ := fun κbar =>
      (a + G / κbar)⁻¹ * C₀ + ((a + G / κbar)⁻¹) ^ 2 * CΔ / κbar
    Tendsto h atTop (𝓝 (C₀ / a)) ∧
      (CΔ ≤ C₀ * G →
        StrictMonoOn h (Set.Ioi 0) ∧
        ∀ κbar : ℝ, 0 < κbar → h κbar < C₀ / a) ∧
      (C₀ * G < CΔ →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧
          StrictMonoOn h (Set.Ioc 0 κ₀) ∧
          StrictAntiOn h (Set.Ici κ₀) ∧
          ∃ K : ℝ, 0 < K ∧ ∀ κbar : ℝ, K ≤ κbar → C₀ / a < h κbar) := by sorry

end AdBlocking.Surplus
