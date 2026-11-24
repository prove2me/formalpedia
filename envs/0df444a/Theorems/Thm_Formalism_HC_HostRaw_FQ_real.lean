-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_FQ_real
-- name    : Formalism.HC.HostRaw.FQ_real
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:27.378858+00:00
-- url     : https://prove2.me/theorems/2fe89501-9b37-47c8-9665-d6adea32021d
-- title:
--   Host Raw: FQ real
-- statement:
--   The Host Raw construction uses the FQ real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L106-L110

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

theorem Formalism.HC.HostRaw.FQ_real (τ : Qb →+* ℂ) {y : Qb} (hy : y ∈ H.FQ) : starRingEnd ℂ (τ y) = τ y := by sorry
