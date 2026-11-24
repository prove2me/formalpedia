-- Prove2me | Theorems.Thm_Formalism_L2_Host_ActsAs_snd
-- name    : Formalism.L2.Host.ActsAs.snd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:53.995466+00:00
-- url     : https://prove2.me/theorems/662352d9-3342-4afa-8e59-c98559522b80
-- title:
--   Acts As: snd
-- statement:
--   The Acts As construction uses the snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L112-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L112-L127

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
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
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.L2.Host.ActsAs.snd {e q d : ℕ} {s : EQ e q d →ₐ[ℚ] Qb} {g : GG e} (h : ActsAs e q d s g)
    (u' : (ZMod (2 ^ (e + 2)))ˣ) (hu' : hcl e u' = g.2) (x : EQ e q d) (z : Qb) (hz : z ∈ mus (2 ^ (e + 2)))
    (hx : (x : Qb) = z + z⁻¹) :
    s x = z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by sorry
