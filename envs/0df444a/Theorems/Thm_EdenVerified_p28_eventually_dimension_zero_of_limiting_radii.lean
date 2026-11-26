-- Prove2me | Theorems.Thm_EdenVerified_p28_eventually_dimension_zero_of_limiting_radii
-- name    : EdenVerified.p28_eventually_dimension_zero_of_limiting_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:42:41.585472+00:00
-- url     : https://prove2.me/theorems/79c45333-3fe1-5944-864c-db4ff66410be
-- title:
--   Eden Verified: p28 eventually dimension zero of limiting radii
-- statement:
--   The Eden Verified construction uses the p28 eventually dimension zero of limiting radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1193-L1199
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1193-L1199

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p28_eventually_dimension_zero_of_limiting_radii :
    ∀ {c : ℝ} (hc : 4 < c)
    (p : PhaseSpace) (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0),
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by sorry
