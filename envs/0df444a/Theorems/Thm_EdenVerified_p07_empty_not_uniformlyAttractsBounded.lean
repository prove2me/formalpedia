-- Prove2me | Theorems.Thm_EdenVerified_p07_empty_not_uniformlyAttractsBounded
-- name    : EdenVerified.p07_empty_not_uniformlyAttractsBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:32:18.89627+00:00
-- url     : https://prove2.me/theorems/4389a6e1-1245-427c-863f-013addeb9b31
-- title:
--   Eden Verified: p07 empty not uniformly Attracts Bounded
-- statement:
--   The Eden Verified construction uses the p07 empty not uniformly Attracts Bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L938-L941
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L938-L941

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p07_empty_not_uniformlyAttractsBounded :
    ∀ (c : ℝ),
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) := by sorry
