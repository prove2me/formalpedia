-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_alt_goal1
-- name    : Bl.general_b_fact_third_alt.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:57.828858+00:00
-- url     : https://prove2.me/theorems/32c54767-a1c9-48b8-8513-2e381f09908d
-- title:
--   general b fact third alt: goal1
-- statement:
--   The general b fact third alt construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdAlt/Imports.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdAlt/Imports.lean#L5-L35

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_alt

theorem Bl.general_b_fact_third_alt.goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {n : Nat}
  (R : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin n → K)) (x : Fin n → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} R)) x →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} R (HSMul.hSMul.{0, 0, 0} d x)) := by sorry
