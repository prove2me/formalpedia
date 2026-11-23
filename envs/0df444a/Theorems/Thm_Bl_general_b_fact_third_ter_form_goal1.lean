-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_ter_form_goal1
-- name    : Bl.general_b_fact_third_ter_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:10.112457+00:00
-- url     : https://prove2.me/theorems/49e22e58-1ba2-4176-bea3-bad262dd31a3
-- title:
--   general b fact third ter form: goal1
-- statement:
--   The general b fact third ter form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdTerForm/Imports.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdTerForm/Imports.lean#L39-L47

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_ter_form

theorem Bl.general_b_fact_third_ter_form.goal1 :
  ∀ {K W : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} W] [inst_3 : Module.{0, 0} K W]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) W]
  [inst_5 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K W]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) W) [hΛ : Submodule.IsLattice.{0, 0, 0} K Λ] (v : W),
  Exists.{1} fun (s : NumberField.RingOfIntegers.{0} K) ↦
    And (Ne.{1} s 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} s v)) := by sorry
