-- Prove2me | Theorems.Thm_BroughanRH_schoenfeldBook
-- name    : BroughanRH.schoenfeldBook
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:11:19.630909+00:00
-- url     : https://prove2.me/theorems/0ab84ea1-0e0e-410a-b016-4c814c646924
-- title:
--   Schoenfeld’s bound in Broughan’s formulation
-- statement:
--   For real $x\ge74$, the absolute error in $\psi(x)$ is at most $\sqrt{x}(\log x)^2/(8\pi)$.
--
--   Lean proof using the named dependencies:
--
--   ```lean
--   by
--     exact fun x hx => (BroughanRH.schoenfeldPsi x (le_trans (by norm_num) hx)).le
--   ```
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 4.9. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem schoenfeldBook :
    ∀ x : ℝ, 74 ≤ x → |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x)^2 / (8 * Real.pi) := by sorry

end BroughanRH
