-- Prove2me | Theorems.Thm_ActuarialValuation_premiumDuePV_first_payment
-- name    : ActuarialValuation.premiumDuePV_first_payment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:37:31.022585+00:00
-- url     : https://prove2.me/theorems/d7b1537c-01b3-4ec4-bae5-b246465375a9
-- title:
--   First premium is certain for a positive term
-- statement:
--   At inception the time-zero premium is always due, independently of mortality. Later payments are nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   n\ge1,\ v\ge0\Longrightarrow Y_n(\omega)\ge1
--   $$
-- source:
--   Dickson, Hardy and Waters (2009 first edition), Actuarial Mathematics for Life Contingent Risks, Chapter 6 §6.4 (net future-loss PV) and §6.5.1, equation (6.1) (net equivalence principle), equation (6.2) (worked endowment net premium); https://doi.org/10.1017/CBO9780511800146; finite n-year assurance from Life Contingencies Ch. 3 §3.2.2 (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
open MeasureTheory

namespace ActuarialValuation

theorem premiumDuePV_first_payment {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    (hn : 0 < n) (hv : 0 ≤ v)
    :
    1 ≤ premiumDuePV K v n ω := by sorry

end ActuarialValuation
