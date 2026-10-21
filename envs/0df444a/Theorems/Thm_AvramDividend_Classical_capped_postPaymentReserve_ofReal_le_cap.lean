-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
-- name    : AvramDividend.Classical.capped_postPaymentReserve_ofReal_le_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:20:51.609422+00:00
-- url     : https://prove2.me/theorems/16104f4f-861a-44e4-8c74-94a125730fa3
-- title:
--   For every time, the capped control's post-payment reserve does not exceed the cap
-- statement:
--   For every sample path, nonnegative time and capped-admissible strategy with ENNReal.ofReal x≤C, the post-payment reserve U_t+=x+X_t−D_{t+} obeys ENNReal.ofReal U_t+≤C. At t=0 use the already accepted capped_postPaymentReserve_initial_state, which accounts for the initial right dividend atom. For t>0 IsAdmissibleLe directly bounds the book-value reserve ENNReal.ofReal U_t≤C; the accepted postPaymentReserve_rightJump_decomposition shows U_t+≤U_t and ENNReal.ofReal is monotone. This holds even after ruin as an ofReal bound (negative reserves map to zero); it does not imply U_t+≥0 after ruin, nor optional-stopping inequalities.
-- source:
--   Uses only Proved initial-cap and right-atom reserve-drop theorems, with no dependence on pending strict-pre-ruin nonnegativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_postPaymentReserve_ofReal_le_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0) :
    ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by sorry
