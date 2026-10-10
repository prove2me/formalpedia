-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserveGain_expected_zero
-- name    : ActuarialValuation.annualReserveGain_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:31:53.513523+00:00
-- url     : https://prove2.me/theorems/985ce25b-e1bb-4011-b17a-11878a4ac39d
-- title:
--   Annual gains are centred under the reserve balance
-- statement:
--   If the one-year expected cashflow plus discounted closing reserve equals the opening reserve, its annual reserve gain has zero expectation.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[C_k]+vR_{k+1}=R_k\Rightarrow\mathbb E[G_k]=0
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_annualReserveGain
import Definitions.Def_actuarial_finiteScenarioExpectation
open MeasureTheory

namespace ActuarialValuation

theorem annualReserveGain_expected_zero {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (C : ℕ → Ω → ℝ) (R : ℕ → ℝ) (v : ℝ) (k : ℕ)
  (hw : (∑ ω : Ω, w ω) = 1)
  (hR : finiteScenarioExpectation w (C k) + v * R (k + 1) = R k)
  :
  finiteScenarioExpectation w (annualReserveGain C R v k) = 0 := by sorry

end ActuarialValuation
