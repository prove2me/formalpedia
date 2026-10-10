-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffExpectedLoss_eq_openingReserve
-- name    : ActuarialValuation.finiteHattendorffExpectedLoss_eq_openingReserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:22:05.277659+00:00
-- url     : https://prove2.me/theorems/2f9e5edf-a000-4b44-8f71-f78a8ad4317c
-- title:
--   Expected insurer loss at issue equals opening reserve
-- statement:
--   With unit scenario mass, the pathwise representation has a deterministic reserve plus a zero-mean risk innovation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[L_n]=V_0
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffExpectedLoss
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteReserveAnnualBalance

namespace ActuarialValuation

theorem finiteHattendorffExpectedLoss_eq_openingReserve {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ) (v : ℝ)
  (premium benefit reserve : ℕ → ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  (hR : ∀ t ∈ Finset.range n,
    finiteReserveAnnualBalance v reserve premium benefit
      (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t)
  :
  finiteHattendorffExpectedLoss w K n v premium benefit reserve = reserve 0 := by sorry

end ActuarialValuation
