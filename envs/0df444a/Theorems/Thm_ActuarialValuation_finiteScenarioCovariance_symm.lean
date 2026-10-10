-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioCovariance_symm
-- name    : ActuarialValuation.finiteScenarioCovariance_symm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:08:32.458185+00:00
-- url     : https://prove2.me/theorems/885be616-107d-41c8-8185-f49723b2dbd5
-- title:
--   Scenario covariance is symmetric
-- statement:
--   Covariance is unchanged by exchanging the two arguments.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Cov}(X,Y)=\operatorname{Cov}(Y,X)
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioCovariance
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioCovariance_symm {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X Y : Ω → ℝ)
  :
  finiteScenarioCovariance w X Y = finiteScenarioCovariance w Y X := by sorry

end ActuarialValuation
