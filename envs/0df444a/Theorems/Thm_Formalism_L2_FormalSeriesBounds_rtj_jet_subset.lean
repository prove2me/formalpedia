-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_subset
-- name    : Formalism.L2.FormalSeriesBounds.rtj_jet_subset
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:09.185314+00:00
-- url     : https://prove2.me/theorems/470ca4c0-aa4c-434d-96cc-a928b41129e2
-- title:
--   Formal Series Bounds: rtj jet subset
-- statement:
--   The Formal Series Bounds construction uses the rtj jet subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L19-L25

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

theorem Formalism.L2.FormalSeriesBounds.rtj_jet_subset (P : MvPolynomial σ K) (F : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    jetAt0 P F = ∑ m ∈ S, MvPolynomial.coeff m P * (mfact m : K) * MvPowerSeries.coeff m F := by sorry
