-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_ActsAs_sqrt_d
-- name    : Formalism.HC.HostRaw.ActsAs.sqrt_d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:00.8429+00:00
-- url     : https://prove2.me/theorems/3d4e3fc6-84cd-4b02-97ff-8d5b3d53d7d6
-- title:
--   Acts As: sqrt d
-- statement:
--   The Acts As construction uses the sqrt d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L133-L147

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

theorem Formalism.HC.HostRaw.ActsAs.sqrt_d {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (h : H.ActsAs s g) (x : H.EQ) (hx : (x : Qb) ∈ sqrts (-(H.d : ℤ))) :
    s x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x := by sorry
