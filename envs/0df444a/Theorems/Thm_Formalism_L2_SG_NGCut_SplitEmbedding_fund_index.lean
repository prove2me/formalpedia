-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_fund_index
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.fund_index
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:15:36.006414+00:00
-- url     : https://prove2.me/theorems/415668db-b97f-4148-af50-48101dfa7078
-- title:
--   Split Embedding: fund index
-- statement:
--   The Split Embedding construction uses the fund index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MassSplit.lean#L81-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MassSplit.lean#L81-L115

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MassSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding

theorem Formalism.L2.SG.NGCut.SplitEmbedding.fund_index {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L Λ : AddSubgroup V) [Countable L] (hle : Λ ≤ L) (k : ℕ)
    (hk : Λ.relIndex L = k) (hk0 : k ≠ 0) (FL FΛ : Set V) (hFL : MeasurableSet FL) (hFΛ : MeasurableSet FΛ)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) (hdΛ : ∀ v, ∃! a : Λ, (a : V) + v ∈ FΛ) :
    μ FΛ = k * μ FL := by sorry
