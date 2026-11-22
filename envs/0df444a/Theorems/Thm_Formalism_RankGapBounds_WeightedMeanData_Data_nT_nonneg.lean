-- Prove2me | Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_nT_nonneg
-- name    : Formalism.RankGapBounds.WeightedMeanData.Data.nT_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:04.144678+00:00
-- url     : https://prove2.me/theorems/d2438d08-df1c-40f6-9c2b-0b847f5c9d17
-- title:
--   Data: n T nonneg
-- statement:
--   The Data construction uses the n T nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean#L149-L150

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
open Formalism.RankGapBounds.WeightedMeanData.Data
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

theorem Formalism.RankGapBounds.WeightedMeanData.Data.nT_nonneg : 0 ≤ D.nT := by sorry
