-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_eCore
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.eCore
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:17.171494+00:00
-- url     : https://prove2.me/theorems/5230dcfb-ea81-4944-a233-fbb25432c4d3
-- title:
--   ring Data Objects: e Core
-- statement:
--   The ring Data Objects construction uses the e Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/IdemFactor.lean#L12-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/IdemFactor.lean#L12-L86

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.eCore {K : Type} [Field K] {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S K) (t : ℕ)
    (α : ℕ → K) (ht : 1 ≤ t)
    (hA : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)))
    (hα : ∀ i j, i < t → j < t → α i = α j → i = j) :
    let EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod
    let δ := ∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)
    EA * EA = δ • EA ∧ EA.rank = 1 ∧ A * EA = α 0 • EA ∧ δ ≠ 0 := by sorry
