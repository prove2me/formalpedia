-- Prove2me | Theorems.Thm_Formalism_L2_N_ExtNRows_finrank_span_image_le
-- name    : Formalism.L2.N.ExtNRows.finrank_span_image_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:34.561341+00:00
-- url     : https://prove2.me/theorems/b3b408c9-8ef2-4a76-9ede-d53671695567
-- title:
--   Ext NRows: finrank span image le
-- statement:
--   The Ext NRows construction uses the finrank span image le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExtNRowsGen.lean#L13-L30

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

theorem Formalism.L2.N.ExtNRows.finrank_span_image_le {n : ℕ} (σ : K →+* ℂ) (j : (Fin n → K) →ₛₗ[σ] W) (A : Submodule K (Fin n → K)) :
    finrank ℂ (Submodule.span ℂ (j '' (A : Set (Fin n → K)))) ≤ finrank K A := by sorry
