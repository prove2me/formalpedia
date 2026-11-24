-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_actsAs_of_one
-- name    : Formalism.HC.HostRaw.actsAs_of_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:33.273797+00:00
-- url     : https://prove2.me/theorems/8103fde4-31da-4c7f-b4a9-1692d51b1e8b
-- title:
--   Host Raw: acts As of one
-- statement:
--   The Host Raw construction uses the acts As of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L114-L119

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

theorem Formalism.HC.HostRaw.actsAs_of_one {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (j : H.E →ₐ[ℚ] Qb)
    (h : ∀ x : H.E, s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)) : H.ActsAs s g := by sorry
