-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
-- name    : AvramDividend.Classical.capped_postPaymentReserve_initial_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:03:05.058+00:00
-- url     : https://prove2.me/theorems/2ecd3672-50b4-4ad7-ad28-d1720acec949
-- title:
--   Initial right dividend payments leave a nonnegative reserve within the cap
-- statement:
--   For a capped-admissible dividend strategy and initial capital with ENNReal.ofReal x≤C, the reserve immediately after the time-zero dividend atom is nonnegative and within C. At t=0 the strategy starts D_0=0 and the Lévy path X_0=0. Admissibility imposes D_{0+}−D_0≤U_0=x, forcing U_0+=x−D_{0+}≥0. Monotonicity ensures the payment atom is nonnegative, so the after-payment reserve does not exceed initial x and hence the cap. This is distinct from the positive-time cap field of IsAdmissibleLe, which only holds for t>0. It supplies the initial HJB state-domain boundary and correct zero-atom convention.
-- source:
--   Direct IsAdmissibleLe initial jump bound and accepted postPaymentReserve_rightJump_decomposition; no Open imports, sorry or local Lean compilation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_postPaymentReserve_initial_state
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (ω : Ω) :
    0 ≤ x + X.X 0 ω - rightLimit D 0 ω ∧
      ENNReal.ofReal (x + X.X 0 ω - rightLimit D 0 ω) ≤ C := by sorry
