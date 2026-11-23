-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_inv_entry_le_one
-- name    : Formalism.DworkPowerSeriesWeights.norm_inv_entry_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:57.498406+00:00
-- url     : https://prove2.me/theorems/9a3444ac-7860-4995-a071-f8890da9f0ec
-- title:
--   Dwork Power Series Weights: norm inv entry le one
-- statement:
--   The Dwork Power Series Weights construction uses the norm inv entry le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean#L54-L64

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

theorem Formalism.DworkPowerSeriesWeights.norm_inv_entry_le_one {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    (h : ∀ i j, ‖M i j‖ ≤ 1) (hd : ‖M.det‖ = 1) (i j : n) : ‖M⁻¹ i j‖ ≤ 1 := by sorry
