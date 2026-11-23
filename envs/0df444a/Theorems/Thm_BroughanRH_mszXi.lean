-- Prove2me | Theorems.Thm_BroughanRH_mszXi
-- name    : BroughanRH.mszXi
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:23.607984+00:00
-- url     : https://prove2.me/theorems/0d660b2e-5106-4e28-842c-fbb729244b32
-- title:
--   Matiyasevich–Saidak–Zvengrowski monotonicity for xi
-- statement:
--   For fixed height $t\ge8$, the modulus of the xi function decreases strictly as the real part increases through $\sigma\le1/2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem mszXi :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ t : ℝ, 8 ≤ t → StrictAntiOn (fun σ : ℝ => ‖xi ((σ : ℂ)+(t : ℂ)*Complex.I)‖) (Set.Iic (1/2 : ℝ)) := by sorry

end BroughanRH
