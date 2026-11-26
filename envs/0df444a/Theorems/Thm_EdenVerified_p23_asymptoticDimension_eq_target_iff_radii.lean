-- Prove2me | Theorems.Thm_EdenVerified_p23_asymptoticDimension_eq_target_iff_radii
-- name    : EdenVerified.p23_asymptoticDimension_eq_target_iff_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:44.760849+00:00
-- url     : https://prove2.me/theorems/930cab29-0c06-5558-8b6a-0f93156d92e4
-- title:
--   Eden Verified: p23 asymptotic Dimension eq target iff radii
-- statement:
--   The Eden Verified construction uses the p23 asymptotic Dimension eq target iff radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1803-L1806
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1803-L1806

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p23_asymptoticDimension_eq_target_iff_radii :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 := by sorry
