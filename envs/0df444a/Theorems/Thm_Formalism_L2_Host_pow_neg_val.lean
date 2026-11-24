-- Prove2me | Theorems.Thm_Formalism_L2_Host_pow_neg_val
-- name    : Formalism.L2.Host.pow_neg_val
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:49.999036+00:00
-- url     : https://prove2.me/theorems/7ecf5066-8e62-4a31-bf9d-9393c018276c
-- title:
--   Host: pow neg val
-- statement:
--   The Host construction uses the pow neg val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L79-L87

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

theorem Formalism.L2.Host.pow_neg_val {N : ℕ} [NeZero N] {z : Qb} (hz : z ^ N = 1) (u : ZMod N) :
    z ^ (-u).val = z⁻¹ ^ u.val := by sorry
