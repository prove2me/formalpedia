-- Prove2me | Theorems.Thm_Bl_general_b_fact_left_tail_goal1
-- name    : Bl.general_b_fact_left_tail.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:15.960575+00:00
-- url     : https://prove2.me/theorems/6600b262-dd60-420e-9180-8d8866eab904
-- title:
--   general b fact left tail: goal1
-- statement:
--   The general b fact left tail construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftTail/Imports.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftTail/Imports.lean#L9-L25

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open Bl Bl.general_b_fact_left_tail
variable {F : Type} [Field F] [NumberField F]

theorem Bl.general_b_fact_left_tail.goal1 (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by sorry
