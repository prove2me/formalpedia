-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_det_le_one_of_entries
-- name    : Formalism.DworkPowerSeriesWeights.norm_det_le_one_of_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:04.926556+00:00
-- url     : https://prove2.me/theorems/2539f4b4-d2d0-43fd-9592-0c35d70816f9
-- title:
--   Dwork Power Series Weights: norm det le one of entries
-- statement:
--   The Dwork Power Series Weights construction uses the norm det le one of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean#L42-L52

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.norm_det_le_one_of_entries {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by sorry
