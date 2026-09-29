-- Prove2me | Theorems.Thm_DysonGraviton_Q_sState
-- name    : DysonGraviton.Q_sState
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:49:17.828368+00:00
-- url     : https://prove2.me/theorems/0ed9fdd6-46ad-40a3-8eb9-10840cdcae74
-- title:
--   Eq. (20) — $Q = \frac45(1 - n/6)$ for the s-state $r^{-n}e^{-r/R}$
-- statement:
--   Let $R > 0$ and $n < 3/2$. For the s-state $f = r^{-n} e^{-r/R}$, $r = \sqrt{s^2+z^2}$ (Eq. (19)), the quadrupole factor of Eq. (16) is
--   $$Q = \frac45\left[1 - \frac n6\right].$$
--   The restriction $n < 3/2$ is the range where both integrals in Eq. (16) converge; the paper leaves it implicit.
-- source:
--   F. Dyson, Is a Graviton Detectable?, Int. J. Mod. Phys. A 28 (2013) 1330041, https://doi.org/10.1142/S0217751X1330041X, p. 7, Eqs. (19)–(20)

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology

namespace DysonGraviton

theorem Q_sState (n R : ℝ) (hR : 0 < R) (hn : n < 3 / 2) :
    Q (sState n R) = 4 / 5 * (1 - n / 6) := by
  sorry

end DysonGraviton
