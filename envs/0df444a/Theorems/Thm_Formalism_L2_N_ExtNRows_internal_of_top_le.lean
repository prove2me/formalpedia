-- Prove2me | Theorems.Thm_Formalism_L2_N_ExtNRows_internal_of_top_le
-- name    : Formalism.L2.N.ExtNRows.internal_of_top_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:24.696912+00:00
-- url     : https://prove2.me/theorems/a2895829-a9ac-5f70-8429-b3de79ccb8f7
-- title:
--   Ext NRows: internal of top le
-- statement:
--   The Ext NRows construction uses the internal of top le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean#L38-L47

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

theorem Formalism.L2.N.ExtNRows.internal_of_top_le {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → Submodule ℂ W) (ht : (⨆ i, B i) = ⊤)
    (hle : ∑ i, finrank ℂ (B i) ≤ finrank ℂ W) : DirectSum.IsInternal B := by sorry
