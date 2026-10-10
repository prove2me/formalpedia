-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffInnovationPointwise
-- name    : ActuarialValuation.finiteHattendorffInnovationPointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:18:50.778595+00:00
-- url     : https://prove2.me/theorems/4634b9e6-6173-48d0-810f-6f16e2b43fc5
-- title:
--   Two actuarial mortality-innovation definitions agree
-- statement:
--   The XIX realised-death-year surprise agrees with XVI's scenario innovation when both use the conditional rate from the same mortality law.
--
--   **Mathematical statement**
--
--   $$
--   I_t^{\mathrm{reserve}}(K_\omega)=I_t^{\mathrm{prob}}(\omega)
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityInnovation
import Definitions.Def_actuarial_finiteReserveYearInnovation

namespace ActuarialValuation

theorem finiteHattendorffInnovationPointwise {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (ω : Ω)
  :
  finiteReserveYearInnovation (K ω) t (finiteMortalityDeathRate w K) =
  finiteMortalityInnovation w K t ω := by sorry

end ActuarialValuation
