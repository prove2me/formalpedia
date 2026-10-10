-- Prove2me | Theorems.Thm_ActuarialValuation_hattendorff_annual_allocation_fundamental
-- name    : ActuarialValuation.hattendorff_annual_allocation_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:19:34.162968+00:00
-- url     : https://prove2.me/theorems/ecc02b8e-0437-4d22-aaa9-40a75d72a9dd
-- title:
--   Hattendorff annual loss allocation capstone
-- statement:
--   Under the reserve balance and pairwise orthogonality of annual gain components, proves zero means, additive discounted variance and the cashflow-reserve telescoping identity.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[G_k]=0,\quad \operatorname{Var}(\sum v^kG_k)=\sum v^{2k}\operatorname{Var}(G_k)
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
import Definitions.Def_actuarial_annualReserveGain
import Definitions.Def_actuarial_discountedAnnualGainSum
import Definitions.Def_actuarial_finiteScenarioCovariance
import Definitions.Def_actuarial_finiteScenarioExpectation
import Definitions.Def_actuarial_finiteScenarioVariance
open MeasureTheory

namespace ActuarialValuation

theorem hattendorff_annual_allocation_fundamental {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (C : ℕ → Ω → ℝ) (R : ℕ → ℝ)
  (v : ℝ) (n : ℕ) (ω : Ω)
  (hw : (∑ a : Ω, w a) = 1)
  (hR : ∀ k ∈ Finset.range n,
    finiteScenarioExpectation w (C k) + v * R (k + 1) = R k)
  (horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
    i ≠ j → finiteScenarioCovariance w (annualReserveGain C R v i)
      (annualReserveGain C R v j) = 0)
  :
  (∀ k ∈ Finset.range n,
      finiteScenarioExpectation w (annualReserveGain C R v k) = 0)
  ∧ (finiteScenarioVariance w
      (discountedAnnualGainSum (annualReserveGain C R v) v n) =
      ∑ k ∈ Finset.range n, v ^ (2 * k) *
        finiteScenarioVariance w (annualReserveGain C R v k))
  ∧ (discountedAnnualGainSum (annualReserveGain C R v) v n ω =
       discountedAnnualGainSum C v n ω + v ^ n * R n - R 0) := by sorry

end ActuarialValuation
