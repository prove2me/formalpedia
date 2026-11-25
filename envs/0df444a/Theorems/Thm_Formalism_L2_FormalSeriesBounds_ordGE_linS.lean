-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_linS
-- name    : Formalism.L2.FormalSeriesBounds.ordGE_linS
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:14.445341+00:00
-- url     : https://prove2.me/theorems/e454cde3-da40-4be8-b4b2-40bc7f57d0ff
-- title:
--   Formal Series Bounds: ord GE lin S
-- statement:
--   The Formal Series Bounds construction uses the ord GE lin S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L184-L188

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.ordGE_linS (M : τ → σ → C) (w : σ) : OrdGE 1 (linS M w) := by sorry
