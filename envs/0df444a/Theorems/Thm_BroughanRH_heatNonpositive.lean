-- Prove2me | Theorems.Thm_BroughanRH_heatNonpositive
-- name    : BroughanRH.heatNonpositive
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:49.800366+00:00
-- url     : https://prove2.me/theorems/8b5f2e0c-d74e-4221-afef-6ee7dcb6d608
-- title:
--   The de Bruijn–Newman constant is nonpositive
-- statement:
--   With the Rodgers–Tao heat-kernel convention, the de Bruijn–Newman constant satisfies $\Lambda\le0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Ch. 5. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib
import Definitions.Def_DeBruijnNewman_core

namespace BroughanRH

theorem heatNonpositive :
    DeBruijnNewman.Lambda ≤ 0 := by sorry

end BroughanRH
