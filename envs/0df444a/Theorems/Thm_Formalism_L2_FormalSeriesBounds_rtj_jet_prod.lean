-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_prod
-- name    : Formalism.L2.FormalSeriesBounds.rtj_jet_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:07.299352+00:00
-- url     : https://prove2.me/theorems/6de0768e-6d4c-44e0-bedb-50d4b7a09e0b
-- title:
--   Formal Series Bounds: rtj jet prod
-- statement:
--   The Formal Series Bounds construction uses the rtj jet prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L176-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L176-L203

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

theorem Formalism.L2.FormalSeriesBounds.rtj_jet_prod {ι : Type} (A : ι → Set σ) (s : Finset ι)
    (hA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    (P : ι → MvPolynomial σ K) (F : ι → MvPowerSeries σ K)
    (hP : ∀ i ∈ s, P i ∈ MvPolynomial.supported K (A i)) (hF : ∀ i ∈ s, rtjSerIn (A i) (F i)) :
    jetAt0 (∏ i ∈ s, P i) (∏ i ∈ s, F i) = ∏ i ∈ s, jetAt0 (P i) (F i) := by sorry
