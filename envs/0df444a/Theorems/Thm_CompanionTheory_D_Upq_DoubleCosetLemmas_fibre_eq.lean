-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_fibre_eq
-- name    : CompanionTheory.D.Upq.DoubleCosetLemmas.fibre_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:19.370988+00:00
-- url     : https://prove2.me/theorems/636b5236-fcb0-4096-817a-03237db2d320
-- title:
--   Double Coset Lemmas: fibre eq
-- statement:
--   The Double Coset Lemmas construction uses the fibre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L22-L34

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.DoubleCosetLemmas
variable {G M : Type} [Group G] [MeasurableSpace M]
variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}

theorem CompanionTheory.D.Upq.DoubleCosetLemmas.fibre_eq {k : G} (hk : k ∈ J) :
    {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = (k * g : G)} = (k * ·) '' stab J g := by sorry
