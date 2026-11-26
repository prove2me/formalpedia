-- Prove2me | Theorems.Thm_EdenVerified_p29_eventually_dimension_formula_zero_two
-- name    : EdenVerified.p29_eventually_dimension_formula_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:23.346159+00:00
-- url     : https://prove2.me/theorems/0e84aa16-2100-415d-8c24-16fca49e1f1a
-- title:
--   Eden Verified: p29 eventually dimension formula zero two
-- statement:
--   The Eden Verified construction uses the p29 eventually dimension formula zero two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1217-L1230
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1217-L1230

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p29_eventually_dimension_formula_zero_two :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧
        limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧
        limitingSquaredRadius (radiusSq₂ p) = 0)),
    ∀ᶠ t in atTop, 0 ≤ normalizedLogSingularValues c t p 0 ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 2 < 0 ∧
      normalizedLogSingularValues c t p 1 < 0 ∧
      finiteTimeDimension c t p = 1 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 1 /
          -normalizedLogSingularValues c t p 1 := by sorry
