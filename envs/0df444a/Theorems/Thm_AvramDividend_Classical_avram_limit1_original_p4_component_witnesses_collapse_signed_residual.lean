-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_p4_component_witnesses_collapse_signed_residual
-- name    : AvramDividend.Classical.avram_limit1_original_p4_component_witnesses_collapse_signed_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:10:14.071826+00:00
-- url     : https://prove2.me/theorems/6a98c6f7-d129-4bf3-ac3c-484ac9493741
-- title:
--   Actual P4 three original source components collapse to integrable signed M/G/H without R L1
-- statement:
--   The canonical original P4-F4 source-components theorem fdb9a6a3 exports three integrable centred martingale terms Mc,Ms,Ml, an integrable nonpositive drift G, and a second nonpositive remainder R. Its statement does NOT assume R is integrable. Prove the correct algebraic collapse: M=Mc+Ms+Ml is integrable and centred by Mathlib integral_add; H=0 is integrable; the sign of R lets us discard it from the a.e. upper inequality. This produces exactly the M,G,H witness shape required by canonical 0dda1be7 and our accepted source-exact LIMIT-1 residual bridge. No additional R integrability, martingale theorem, equality-in-law, or circular canonical import is assumed; all P4 stochastic witnesses remain an explicit hSource premise.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_p4_component_witnesses_collapse_signed_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (wInit : ℝ) (Cash Term : Ω → ℝ)
    (hSource : ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        wInit + Mc ω + Ms ω + Ml ω + G ω + R ω)) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ wInit + M ω + G ω + H ω) := by sorry
