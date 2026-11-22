-- Prove2me | Theorems.Thm_Bl_NearbyExistence_goal1
-- name    : Bl.NearbyExistence.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:08.834456+00:00
-- url     : https://prove2.me/theorems/40067673-a296-428b-b242-822a56f9816c
-- title:
--   Nearby Existence: goal1
-- statement:
--   The Nearby Existence construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/NearbyExistence/ExistsNear.lean#L18-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/NearbyExistence/ExistsNear.lean#L18-L58

import Mathlib
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.NearbyExistence

theorem Bl.NearbyExistence.goal1 :
  ∀ {F : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F))
  (x :
    Subtype.{1} fun (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} F v) ↦
      Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.{0, 0} F v) x),
  Exists.{1} fun (r : NumberField.RingOfIntegers.{0} F) ↦
    LT.lt.{0}
      (DFunLike.coe.{1, 1, 1} Valued.v.{0, 0}
        (HSub.hSub.{0, 0, 0} (Subtype.val.{1} x)
          (DFunLike.coe.{1, 1, 1}
            (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} F)
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion.{0, 0} F v))
            r)))
      1 := by sorry
