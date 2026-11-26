-- Prove2me | Theorems.Thm_EdenVerified_p06_infDist_evolution_attractor_sq_le
-- name    : EdenVerified.p06_infDist_evolution_attractor_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:37.637553+00:00
-- url     : https://prove2.me/theorems/aeec4ec6-c468-52af-bdd3-3eb707c77d6b
-- title:
--   Eden Verified: p06 inf Dist evolution attractor sq le
-- statement:
--   The Eden Verified construction uses the p06 inf Dist evolution attractor sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L917-L923
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L917-L923

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p06_infDist_evolution_attractor_sq_le :
    ∀ (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W),
    Metric.infDist (evolution c t p) attractor ^ 2 ≤ attractionBound c M W t := by sorry
