-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward47_real_integrable_of_lintegral_ENNReal_dominator
-- name    : AvramDividend.Classical.avram_pj_reward47_real_integrable_of_lintegral_ENNReal_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:06:22.072688+00:00
-- url     : https://prove2.me/theorems/d95b2a3c-c5b6-4e82-9c90-041481767ef2
-- title:
--   Finite ENNReal mass envelope gives L1 integrability of a dominated real-valued stopped source
-- statement:
--   A measurable nonnegative extended-real random mass with finite expected mass yields L1 integrability of any AEStronglyMeasurable real random gain pointwise bounded in absolute value by a fixed nonnegative multiple of the toReal mass. Reuse for original stopped marked Lévy finite-band source after proving physical measurability and count domination.
-- source:
--   Mathlib integrable_toReal_of_lintegral_ne_top and Integrable.mono in pinned Mathlib revision; source43 provides actual finite expected marked count.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward47_real_integrable_of_lintegral_ENNReal_dominator
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → ℝ≥0∞)
    (hFm : AEMeasurable F P)
    (hFi : (∫⁻ ω, F ω ∂P) < ⊤)
    (g : Ω → ℝ) (hgm : AEStronglyMeasurable g P)
    (K : ℝ) (hK : 0 ≤ K)
    (hDom : ∀ᵐ ω ∂P, |g ω| ≤ K * (F ω).toReal) :
    Integrable g P := by sorry
