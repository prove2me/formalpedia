-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualPremium_scale
-- name    : ActuarialValuation.decrementAnnualPremium_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:08:42.402425+00:00
-- url     : https://prove2.me/theorems/90e44bb0-f9e0-4253-82e7-877b4837ecd1
-- title:
--   Scaling all benefits and reserves scales required premiums
-- statement:
--   A common monetary scale multiplies death benefits, reserves and required premium, leaving transition probabilities fixed.
--
--   **Mathematical statement**
--
--   $$
--   \Pi(ab,aR,aR_+)=a\Pi(b,R,R_+)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
open MeasureTheory

namespace ActuarialValuation

theorem decrementAnnualPremium_scale {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ) (a : ℝ)
  :
  decrementAnnualPremium p q (fun j => a * b j) v (a * R) (a * Rnext) =
    a * decrementAnnualPremium p q b v R Rnext := by sorry

end ActuarialValuation
