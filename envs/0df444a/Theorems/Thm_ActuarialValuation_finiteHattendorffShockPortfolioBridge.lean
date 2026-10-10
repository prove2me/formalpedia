-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffShockPortfolioBridge
-- name    : ActuarialValuation.finiteHattendorffShockPortfolioBridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:19:38.574511+00:00
-- url     : https://prove2.me/theorems/677e9033-06b1-40cd-ab06-fbc43cd0bb01
-- title:
--   Reserve-loss and finite probability innovation sums coincide
-- statement:
--   Pointwise equality of annual innovations makes the time-zero discounted reserve-risk portfolio equal to the XVI finite-scenario shock sum.
--
--   **Mathematical statement**
--
--   $$
--   Z_n^{\mathrm{reserve}}(K_\omega)=Z_n^{\mathrm{prob}}(\omega)
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteReserveInnovationValue

namespace ActuarialValuation

theorem finiteHattendorffShockPortfolioBridge {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ) (v : ℝ)
  (benefit reserve : ℕ → ℝ) (ω : Ω)
  :
  finiteReserveInnovationValue (K ω) n v benefit reserve (finiteMortalityDeathRate w K) =
  finiteMortalityDiscountedShock w K (finiteHattendorffNetAtRisk v benefit reserve) n ω := by sorry

end ActuarialValuation
