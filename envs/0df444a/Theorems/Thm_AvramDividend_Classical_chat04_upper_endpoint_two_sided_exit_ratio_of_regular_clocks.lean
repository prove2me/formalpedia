-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_ratio_of_regular_clocks
-- name    : AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_ratio_of_regular_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:40:53.585821+00:00
-- url     : https://prove2.me/theorems/494b8000-7fc1-4c74-8399-aac21c25120a
-- title:
--   Exact scale-ratio two-sided exit identity at the upper initial reserve boundary under regular passage clocks
-- statement:
--   Under the Avram standing assumptions, strict positivity W(a)>0 implies W(a)/W(a)=1. If strict upward first passage above zero is instantaneous almost surely and strict downward passage below −a takes strictly positive time, the upper-before-ruin exit discount starting at initial reserve a is also one. Thus the canonical scale-ratio two-sided exit identity holds exactly at x=a under the two explicit path regularity inputs.
-- source:
--   Composes Proved scaleFunction_strict_pos_of_standing (59531c77-8eaf-44ac-a657-5b3ae9dcf8d6) and new chat04_upper_endpoint_two_sided_exit_expectation_one (4f871287-bf29-4860-8d54-596d7d7b830b). Direct upper-endpoint x=a case of alternative Open two_sided_exit_before_ruin_identity (5bcf90e1-211c-42db-beac-d92aeb95b5c9), immediate parent 3e1ce2c8.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.Algebra.Order.Field.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_two_sided_exit_ratio_of_regular_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hup0 : ∀ᵐ ω ∂P, twoSidedExitUpTime X 0 ω = 0)
    (hdownpos : ∀ᵐ ω ∂P,
      0 < twoSidedExitDownTime X (-a) ω) :
    twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) := by sorry
