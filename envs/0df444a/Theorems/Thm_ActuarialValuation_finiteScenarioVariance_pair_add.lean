-- Prove2me | Theorems.Thm_ActuarialValuation_finiteScenarioVariance_pair_add
-- name    : ActuarialValuation.finiteScenarioVariance_pair_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:17:53.552098+00:00
-- url     : https://prove2.me/theorems/18d2a775-279a-403a-96f0-84ee73aa7697
-- title:
--   Orthogonality removes the variance cross-term
-- statement:
--   The covariance term in the variance of a sum vanishes when the two gains are uncorrelated.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Cov}(X,Y)=0\Rightarrow\operatorname{Var}(X+Y)=\operatorname{Var}(X)+\operatorname{Var}(Y)
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_finiteScenarioCovariance
import Definitions.Def_actuarial_finiteScenarioVariance
open MeasureTheory

namespace ActuarialValuation

theorem finiteScenarioVariance_pair_add {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X Y : Ω → ℝ)
  (hcov : finiteScenarioCovariance w X Y = 0)
  :
  finiteScenarioVariance w (fun ω => X ω + Y ω) =
    finiteScenarioVariance w X + finiteScenarioVariance w Y := by sorry

end ActuarialValuation
