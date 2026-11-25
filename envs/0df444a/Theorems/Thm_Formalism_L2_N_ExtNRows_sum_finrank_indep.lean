-- Prove2me | Theorems.Thm_Formalism_L2_N_ExtNRows_sum_finrank_indep
-- name    : Formalism.L2.N.ExtNRows.sum_finrank_indep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:19.970415+00:00
-- url     : https://prove2.me/theorems/47d136a0-b431-42c0-bb0f-051a3b690161
-- title:
--   Ext NRows: sum finrank indep
-- statement:
--   The Ext NRows construction uses the sum finrank indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean#L32-L36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExtNRowsGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.N Formalism.L2.N.ExtNRows
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem Formalism.L2.N.ExtNRows.sum_finrank_indep {ι : Type} [Fintype ι] (B : ι → Submodule ℂ W) (hi : iSupIndep B) :
    ∑ i, finrank ℂ (B i) = finrank ℂ (⨆ i, B i : Submodule ℂ W) := by sorry
