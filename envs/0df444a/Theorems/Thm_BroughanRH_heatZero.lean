-- Prove2me | Theorems.Thm_BroughanRH_heatZero
-- name    : BroughanRH.heatZero
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:46.36901+00:00
-- url     : https://prove2.me/theorems/a2ed18c3-a948-4033-8ea8-a3d7e1854aa9
-- title:
--   The de Bruijn–Newman constant vanishes
-- statement:
--   The constant is exactly zero. The platform’s accepted Rodgers–Tao lower bound supplies one direction. [Source](https://prove2.me/theorems/a5dad6cf-f790-4169-a742-2bcdcc8c9c6a).
--
--   Lean proof using the named dependencies:
--
--   ```lean
--   by
--     exact le_antisymm BroughanRH.heatNonpositive DeBruijnNewman.debruijn_newman_constant_nonneg.1
--   ```
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §4.9; Thm. 5.9. https://doi.org/10.1017/9781009384780

import Mathlib
import Definitions.Def_DeBruijnNewman_core

namespace BroughanRH

theorem heatZero :
    DeBruijnNewman.Lambda = 0 := by sorry

end BroughanRH
