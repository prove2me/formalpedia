-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveInnovationValue_succ
-- name    : ActuarialValuation.finiteReserveInnovationValue_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:08:52.242149+00:00
-- url     : https://prove2.me/theorems/05504e5e-90a6-4bf5-8e85-2456b6bb0ae4
-- title:
--   Innovation portfolio adds one year's net amount at risk
-- statement:
--   Extending the horizon adds precisely the discounted policy-year innovation term.
--
--   **Mathematical statement**
--
--   $$
--   Z_{n+1}=Z_n+v^{n+1}(b_{n+1}-V_{n+1})I_n
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveInnovationValue
import Definitions.Def_actuarial_finiteReserveYearInnovation
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveInnovationValue_succ (K n : ℕ) (v : ℝ) (benefit reserve q : ℕ → ℝ)
  :
  finiteReserveInnovationValue K (n + 1) v benefit reserve q =
  finiteReserveInnovationValue K n v benefit reserve q +
  v ^ (n + 1) * (benefit (n + 1) - reserve (n + 1)) *
    finiteReserveYearInnovation K n q := by sorry

end ActuarialValuation
