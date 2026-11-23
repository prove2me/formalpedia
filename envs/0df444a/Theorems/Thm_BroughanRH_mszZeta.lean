-- Prove2me | Theorems.Thm_BroughanRH_mszZeta
-- name    : BroughanRH.mszZeta
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:23:29.353181+00:00
-- url     : https://prove2.me/theorems/c135bb17-d919-41cf-904e-043a5b360730
-- title:
--   Matiyasevich–Saidak–Zvengrowski monotonicity for zeta
-- statement:
--   For fixed height $t\ge8$, the modulus of the zeta function decreases strictly as the real part increases through $\sigma\le1/2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem mszZeta :
    ∀ t : ℝ, 8 ≤ t → StrictAntiOn (fun σ : ℝ => ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖) (Set.Iic (1/2 : ℝ)) := by sorry

end BroughanRH
