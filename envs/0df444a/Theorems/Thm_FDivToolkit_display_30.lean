-- Prove2me | Theorems.Thm_FDivToolkit_display_30
-- name    : FDivToolkit.display_30
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:05.763023+00:00
-- url     : https://prove2.me/theorems/604ab3f2-5d29-47e8-9762-ed9901a33647
-- title:
--   Display (30), proof of Proposition 2, p.32
-- statement:
--   Let $H$ be a generating function and $F$ the function of (2). For all $y>1$,
--   $$
--   F(y)\le(y-1)H(\log y)\le y\,H(\log y).
--   $$
--
--   This upper bound on $F$ turns tail control of $H(\log(g/f))$ into finiteness of the divergence in Proposition 2.
--
--   Differences from the source: none.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (30), proof of Proposition 2, p.32

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_Fh

namespace FDivToolkit

/-- Display (30), Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of Proposition 2,
p.32: for all `y > 1`, `F(y) ≤ (y − 1) H(log y) ≤ y H(log y)`. -/
theorem display_30 {H : ℝ → ℝ} (hH : IsAdmissibleH H) (y : ℝ) (hy : 1 < y) :
    Fh H y ≤ (y - 1) * H (Real.log y) ∧ (y - 1) * H (Real.log y) ≤ y * H (Real.log y) := by sorry

end FDivToolkit
