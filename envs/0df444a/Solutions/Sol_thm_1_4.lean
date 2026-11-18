-- Prove2me | solution 1 for thm_1_4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:17:34.047209+00:00
-- url     : https://prove2.me/submissions/5a87b7f8-da15-4742-bb92-ecc8d1a45173

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F000
import Theorems.Thm_Thm_1_4_rsTaggedCommonLimit_integral_deriv
import Theorems.Thm_taggedCommonLimit_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory DarbouxRS Thm_1_4
open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hαmono : MonotoneOn α (Icc a b))
    (hαderiv : ∀ x ∈ Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Icc a b))
    (hRS : RSIntegrable f α a b) :
    IntervalIntegrable (fun x => f x * α' x) volume a b ∧
      rsIntegral f α a b hRS = ∫ x in a..b, f x * α' x := by
  have hInt :
      IntervalIntegrable (fun x => f x * α' x) volume a b :=
    (hf.mul hα'cont).intervalIntegrable_of_Icc hab
  have hstrict : a < b :=
    Thm_1_4.strict_interval_of_rsIntegrable hRS
  have hTagged :
      rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) :=
    Thm_1_4.rsTaggedCommonLimit_integral_deriv
      hstrict hf hαmono hαderiv hα'cont
  refine ⟨hInt, ?_⟩
  exact taggedCommonLimit_unique (rsIntegral_spec hRS) hTagged
