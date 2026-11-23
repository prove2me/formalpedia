-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_finite
-- name    : CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:25.632038+00:00
-- url     : https://prove2.me/theorems/976e7eec-37b0-41ca-952b-bc773ef3ff33
-- title:
--   Meas: finite
-- statement:
--   The Meas construction uses the finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L54-L59

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

theorem CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.finite (h : Meas dx φ J g) : (cos J g J).Finite := by sorry
