-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_rank_diag_ite
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.rank_diag_ite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:55.830364+00:00
-- url     : https://prove2.me/theorems/9f5cc754-a0f7-45a9-9d72-3ba395edbc59
-- title:
--   ring Data Objects: rank diag ite
-- statement:
--   The ring Data Objects construction uses the rank diag ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/RankDiagIte.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/RankDiagIte.lean#L44-L48

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CMemPolyT
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_BurnsideMat
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte
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

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.rank_diag_ite {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] :
    (Matrix.diagonal fun a => if S a then (1 : K) else 0).rank = Nat.card {a // S a} := by sorry
