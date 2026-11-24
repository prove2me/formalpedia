-- Prove2me | Theorems.Thm_Formalism_L2_Host_restr_apply
-- name    : Formalism.L2.Host.restr_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:54.591654+00:00
-- url     : https://prove2.me/theorems/33e07c52-5ffc-4c48-babe-ac62df6834e1
-- title:
--   Host: restr apply
-- statement:
--   The Host construction uses the restr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RealCyclotomicTwoPower.lean#L43-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/RealCyclotomicTwoPower.lean#L43-L43

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
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

theorem Formalism.L2.Host.restr_apply (L : Fld) (s : Qb ≃ₐ[ℚ] Qb) (x : L) : restr L s x = s x := by sorry

attribute [defeq] Formalism.L2.Host.restr_apply
