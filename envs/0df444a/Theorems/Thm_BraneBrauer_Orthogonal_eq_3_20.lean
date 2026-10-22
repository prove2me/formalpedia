-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_eq_3_20
-- name    : BraneBrauer.Orthogonal.eq_3_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:34.021203+00:00
-- url     : https://prove2.me/theorems/e8ff89df-60b9-4aaf-8ed2-a88d29041010
-- title:
--   (3.20) — partial transpose preserves the trace pairing
-- statement:
--   For two operators $X,Y$ on the mixed tensor space, the partial transpose $\Sigma$ preserves their trace pairing:
--   $$
--   \operatorname{tr}_{m,n}(XY)
--   =\operatorname{tr}_{m,n}(\Sigma(X)\Sigma(Y)).
--   $$
--   This is the bilinear-form identity used to pass from the third to the fourth line of (7.13).
--
--   **Formalization Note** The paper writes this on a complete Brauer basis. Matrix bilinearity extends it to all operators, the domain used here.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 12, (3.20)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section

namespace BraneBrauer.Orthogonal

/-- (3.20), p. 12: the partial transpose preserves the trace
bilinear form, extended from Brauer basis elements to all operators. -/
theorem eq_3_20 {N m n : ℕ} (X Y : Op N m n) :
    (X * Y).trace = (sigma X * sigma Y).trace := by sorry

end BraneBrauer.Orthogonal
