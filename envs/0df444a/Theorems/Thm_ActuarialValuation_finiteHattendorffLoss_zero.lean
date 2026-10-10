-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHattendorffLoss_zero
-- name    : ActuarialValuation.finiteHattendorffLoss_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:07:06.899972+00:00
-- url     : https://prove2.me/theorems/79d1e776-5d26-4f6c-94cd-98b85f6be95b
-- title:
--   Issue-date loss at a zero-term horizon equals opening reserve
-- statement:
--   With no policy years covered, the original and scenario-wrapped finite-loss definition both reduce to the opening reserve.
--
--   **Mathematical statement**
--
--   $$
--   L_0(\omega)=V_0
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 320 (pp. 319–323), Shiu–Xiong (2021), equations (1)–(5), fully discrete loss and prospective-reserve recursion; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLoss

namespace ActuarialValuation

theorem finiteHattendorffLoss_zero {Ω : Type*} [Fintype Ω] (K : Ω → ℕ) (v : ℝ) (premium benefit reserve : ℕ → ℝ) (ω : Ω)
  :
  finiteHattendorffLoss K 0 v premium benefit reserve ω = reserve 0 := by sorry

end ActuarialValuation
