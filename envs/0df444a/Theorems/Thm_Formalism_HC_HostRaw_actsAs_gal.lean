-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_actsAs_gal
-- name    : Formalism.HC.HostRaw.actsAs_gal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:54.064702+00:00
-- url     : https://prove2.me/theorems/ed0c63e5-e838-434c-9e9d-bcb92a35d9cb
-- title:
--   Host Raw: acts As gal
-- statement:
--   The Host Raw construction uses the acts As gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L151-L155

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
variable (H)

theorem Formalism.HC.HostRaw.actsAs_gal (j : H.E →ₐ[ℚ] Qb) (σ : H.E ≃ₐ[ℚ] H.E) :
    H.ActsAs ((j.comp (σ : H.E →ₐ[ℚ] H.E)).comp ((H.jOf j).symm : H.EQ →ₐ[ℚ] H.E)) (H.gal σ) := by sorry
