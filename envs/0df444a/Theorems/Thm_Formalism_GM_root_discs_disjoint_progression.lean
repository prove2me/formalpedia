-- Prove2me | Theorems.Thm_Formalism_GM_root_discs_disjoint_progression
-- name    : Formalism.GM.root_discs_disjoint_progression
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:39.454198+00:00
-- url     : https://prove2.me/theorems/8d169e0a-0b5b-4fc4-9ed5-aa1e9fa36bac
-- title:
--   GM: root discs disjoint progression
-- statement:
--   The GM construction uses the root discs disjoint progression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L181-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean#L181-L232

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open ArithmeticProgressionDivisibility
open Classical

theorem Formalism.GM.root_discs_disjoint_progression : DiscsDisjointAP := by sorry
