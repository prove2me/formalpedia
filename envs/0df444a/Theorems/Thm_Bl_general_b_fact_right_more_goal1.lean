-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_more_goal1
-- name    : Bl.general_b_fact_right_more.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:41.2218+00:00
-- url     : https://prove2.me/theorems/cbdc875e-9ef9-494a-a3e0-c1fc970f5dfe
-- title:
--   general b fact right more: goal1
-- statement:
--   The general b fact right more construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightMore/Imports.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightMore/Imports.lean#L5-L35

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_more

theorem Bl.general_b_fact_right_more.goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] [StarRing.{0} E]
  (P : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} E)),
  Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
    And (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) a)
      (Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Not (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) c))
          (∀ (p : NumberField.RingOfIntegers.{0} E),
            Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) p →
              Exists.{1} fun (t : NumberField.RingOfIntegers.{0} E) ↦
                Eq.{1} (HMul.hMul.{0, 0, 0} c p) (HMul.hMul.{0, 0, 0} a t)))  := by sorry
