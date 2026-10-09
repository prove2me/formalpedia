-- Prove2me | Theorems.Thm_ActuarialValuation_discountedAnnualGain_variance_orthogonal
-- name    : ActuarialValuation.discountedAnnualGain_variance_orthogonal
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:18:51.787151+00:00
-- url     : https://prove2.me/theorems/0e3e8fb2-818e-469f-8b98-d4d70678d2e7
-- title:
--   Finite Hattendorff variance identity for orthogonal annual gains
-- statement:
--   Pairwise zero covariance eliminates all cross-year variance terms, without assuming independence.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(\sum_{k<n}v^kG_k)=\sum_{k<n}v^{2k}\operatorname{Var}(G_k)
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_discountedAnnualGainSum
import Definitions.Def_actuarial_finiteScenarioCovariance
import Definitions.Def_actuarial_finiteScenarioVariance
open MeasureTheory

namespace ActuarialValuation

theorem discountedAnnualGain_variance_orthogonal {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (G : ℕ → Ω → ℝ) (v : ℝ) (n : ℕ)
  (horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
    i ≠ j → finiteScenarioCovariance w (G i) (G j) = 0)
  :
  finiteScenarioVariance w (discountedAnnualGainSum G v n) =
    ∑ k ∈ Finset.range n, v ^ (2 * k) * finiteScenarioVariance w (G k) := by sorry

end ActuarialValuation
