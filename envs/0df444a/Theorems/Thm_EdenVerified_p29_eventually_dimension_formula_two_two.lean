-- Prove2me | Theorems.Thm_EdenVerified_p29_eventually_dimension_formula_two_two
-- name    : EdenVerified.p29_eventually_dimension_formula_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:24.369803+00:00
-- url     : https://prove2.me/theorems/850cb8c0-9027-52a0-bedf-ff4c36f20b6b
-- title:
--   Eden Verified: p29 eventually dimension formula two two
-- statement:
--   The Eden Verified construction uses the p29 eventually dimension formula two two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1232-L1244
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1232-L1244

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p29_eventually_dimension_formula_two_two :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2),
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < 2 → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 3 < 0 ∧
      normalizedLogSingularValues c t p 2 < 0 ∧
      finiteTimeDimension c t p = 2 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 2 /
          -normalizedLogSingularValues c t p 2 := by sorry
