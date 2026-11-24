-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_ActsAs_label_unique
-- name    : Formalism.HC.HostRaw.ActsAs.label_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:32.543911+00:00
-- url     : https://prove2.me/theorems/27923592-8dd1-48bd-8b20-20cdb2a354b3
-- title:
--   Acts As: label unique
-- statement:
--   The Acts As construction uses the label unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L127-L131

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)
variable {H}

theorem Formalism.HC.HostRaw.ActsAs.label_unique {s : H.EQ →ₐ[ℚ] Qb} {g g' : φ.GG} (h : H.ActsAs s g) (h' : H.ActsAs s g') : g = g' := by sorry
