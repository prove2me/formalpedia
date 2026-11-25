-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_rename
-- name    : Formalism.L2.FormalSeriesBounds.rtj_jet_rename
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:44.350808+00:00
-- url     : https://prove2.me/theorems/34612cfd-f051-4031-ac6a-e67e8a8905dc
-- title:
--   Formal Series Bounds: rtj jet rename
-- statement:
--   The Formal Series Bounds construction uses the rtj jet rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L233-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L233-L257

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
variable {K : Type} [Field K] {σ τ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_jet_rename (e : σ ↪ τ) (P : MvPolynomial σ K) (F : MvPowerSeries σ K) :
    jetAt0 (MvPolynomial.rename e P) (MvPowerSeries.rename e F) = jetAt0 P F := by sorry
