-- Prove2me | Theorems.Thm_BroughanRH_mszEta
-- name    : BroughanRH.mszEta
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:14.814008+00:00
-- url     : https://prove2.me/theorems/490dbde9-05a4-4b47-8f32-190866a95c09
-- title:
--   Matiyasevich–Saidak–Zvengrowski monotonicity for eta
-- statement:
--   For fixed height $t\ge8$, the modulus of the eta function decreases strictly as the real part increases through $\sigma\le1/2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem mszEta :
    ∀ t : ℝ, 8 ≤ t → StrictAntiOn (fun σ : ℝ => ‖(fun s : ℂ => (1 - (2 : ℂ)^(1-s))*riemannZeta s) ((σ : ℂ)+(t : ℂ)*Complex.I)‖) (Set.Iic (1/2 : ℝ)) := by sorry

end BroughanRH
