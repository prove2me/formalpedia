-- Prove2me | Theorems.Thm_ActuarialValuation_csShock_observed_tie
-- name    : ActuarialValuation.csShock_observed_tie
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:44.766996+00:00
-- url     : https://prove2.me/theorems/2f53ae13-cff8-4b52-b063-bca17d6c7caa
-- title:
--   Actual joint-lifetime events and cause partition: csShock_observed_tie
-- statement:
--   An earliest common shock causes exact simultaneous observed deaths, even if primitive times themselves are distinct.
--
--   Mathematical relation:
--
--   $$
--   csShock\_observed\_tie
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstLife
import Definitions.Def_actuarial_csSecondLife

namespace ActuarialValuation

theorem csShock_observed_tie {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (ω : Ω) (hzu : Z ω < U ω) (hzv : Z ω < V ω) : csFirstLife U Z ω = csSecondLife V Z ω := by sorry

end ActuarialValuation
