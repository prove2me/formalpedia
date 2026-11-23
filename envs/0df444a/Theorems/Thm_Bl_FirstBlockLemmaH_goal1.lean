-- Prove2me | Theorems.Thm_Bl_FirstBlockLemmaH_goal1
-- name    : Bl.FirstBlockLemmaH.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:05.8608+00:00
-- url     : https://prove2.me/theorems/180cdeba-e05a-4d24-999b-b814fdb7d973
-- title:
--   First Block Lemma H: goal1
-- statement:
--   The First Block Lemma H construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaH/Imports.lean#L5-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaH/Imports.lean#L5-L45

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaH

theorem Bl.FirstBlockLemmaH.goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V] {ι : Type} [Fintype.{0} ι] [DecidableEq.{1} ι]
  {b : Module.Basis.{0, 0, 0} ι E V} {M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V},
  Module.Finite.{0, 0} (NumberField.RingOfIntegers.{0} E) (Subtype.{1} fun (x : V) ↦ Membership.mem.{0, 0} M x) →
    Exists.{1} fun (s : NumberField.RingOfIntegers.{0} E) ↦
      And (Membership.mem.{0, 0} (nonZeroDivisors.{0} (NumberField.RingOfIntegers.{0} E)) s)
        (∀ (v : V),
          Membership.mem.{0, 0} M v →
            ∀ (i : ι),
              Membership.mem.{0, 0}
                (RingHom.range.{0, 0} (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} E) E))
                (HMul.hMul.{0, 0, 0}
                  (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} E) E) s)
                  (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Module.Basis.repr.{0, 0, 0} b) v) i))) := by sorry
