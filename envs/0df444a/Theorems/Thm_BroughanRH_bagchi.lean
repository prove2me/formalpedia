-- Prove2me | Theorems.Thm_BroughanRH_bagchi
-- name    : BroughanRH.bagchi
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:55.596+00:00
-- url     : https://prove2.me/theorems/cf5ef29c-5322-4cd0-950d-f99a2266d265
-- title:
--   Bagchi’s strong recurrence of zeta
-- statement:
--   On each compact subset of the open right half of the critical strip, imaginary shifts approximate zeta uniformly with positive lower density for each positive tolerance.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III Thm. 9.19. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem bagchi :
    ∀ K : Set ℂ, IsCompact K → (∀ s ∈ K, 1/2 < s.re ∧ s.re < 1) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T : ℝ in Filter.atTop,
        δ * T ≤ (MeasureTheory.volume {t : ℝ | t ∈ Set.Icc 0 T ∧
          ∀ s ∈ K, ‖riemannZeta (s + (t : ℂ) * Complex.I) - riemannZeta s‖ < ε}).toReal := by sorry

end BroughanRH
