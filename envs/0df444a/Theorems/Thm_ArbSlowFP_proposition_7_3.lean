-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_7_3
-- name    : ArbSlowFP.proposition_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:41.456828+00:00
-- url     : https://prove2.me/theorems/9055f287-0bfd-4ca3-a737-22bcde193137
-- title:
--   Proposition 7.3 — the RPS clock satisfies Definition 6.2 with $\tau=1$, $c_{\mathrm{ref}}=1/2$, $\ell_*=0$, $a_P=(2,2,2)^\top/27$
-- statement:
--   The clock of Proposition 5.1 satisfies Definition 6.2 with
--   $$\tau=1,\quad c_{\mathrm{ref}}=\tfrac12,\quad \ell_*=(0,0,0),\quad a_P=\tfrac1{27}(2,2,2)^\top,$$
--   at the baseline $H=A_2+3=4$. This supplies the additional data for the first lift.
--
--   Differences from the source:
--   none.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.47, Proposition 7.3

import Mathlib
import Definitions.Def_ArbSlowFP_rpsClockData
import Definitions.Def_ArbSlowFP_IsAddData

open Matrix

namespace ArbSlowFP

/-- Proposition 7.3, p.47 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): the clock
of Proposition 5.1 satisfies Definition 6.2 with `τ = 1`, `cref = 1/2`, `ℓ∗ = (0, 0, 0)`,
`a_P = (2, 2, 2)⊤/27`, where `H = A₂ + 3 = 4`. -/
theorem proposition_7_3 :
    IsAddData rpsClockData.parent (rpsClockData.Ak + 3) 1 (1 / 2) (fun _ => 0) (fun _ => 2 / 27) := by sorry

end ArbSlowFP
