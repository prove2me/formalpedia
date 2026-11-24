-- Prove2me | Theorems.Thm_Formalism_L2_Host_ActsAs_unique
-- name    : Formalism.L2.Host.ActsAs.unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:33.719834+00:00
-- url     : https://prove2.me/theorems/81cb6114-9902-4ad9-8dad-9bf93a810c3a
-- title:
--   Acts As: unique
-- statement:
--   The Acts As construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L89-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L89-L110

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

theorem Formalism.L2.Host.ActsAs.unique {e q d : ℕ} {s s' : EQ e q d →ₐ[ℚ] Qb} {g : GG e}
    (h : ActsAs e q d s g) (h' : ActsAs e q d s' g) : s = s' := by sorry
