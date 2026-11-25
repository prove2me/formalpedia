-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_one
-- name    : Formalism.L2.FormalSeriesBounds.rtj_jet_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:02.241831+00:00
-- url     : https://prove2.me/theorems/2d49459b-8824-4298-b0eb-affedeaf833a
-- title:
--   Formal Series Bounds: rtj jet one
-- statement:
--   The Formal Series Bounds construction uses the rtj jet one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L165-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L165-L174

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_jet_one : jetAt0 (1 : MvPolynomial σ K) (1 : MvPowerSeries σ K) = 1 := by sorry
