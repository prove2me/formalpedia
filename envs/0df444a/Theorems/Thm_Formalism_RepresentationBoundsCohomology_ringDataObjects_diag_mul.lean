-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_diag_mul
-- name    : Formalism.RepresentationBoundsCohomology.ringDataObjects.diag_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:35.640133+00:00
-- url     : https://prove2.me/theorems/3960ed52-2ff3-4e37-89fe-ba16793b2e19
-- title:
--   ring Data Objects: diag mul
-- statement:
--   The ring Data Objects construction uses the diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/RankDiagIte.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/RankDiagIte.lean#L28-L34

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
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)

theorem Formalism.RepresentationBoundsCohomology.ringDataObjects.diag_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (i : d)
    (hi : ∀ l, bl i = bl l → i = l) : (M * N) i i = M i i * N i i := by sorry
