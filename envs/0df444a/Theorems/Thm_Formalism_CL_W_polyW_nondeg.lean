-- Prove2me | Theorems.Thm_Formalism_CL_W_polyW_nondeg
-- name    : Formalism.CL.W.polyW_nondeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:50.339045+00:00
-- url     : https://prove2.me/theorems/4d21facb-1054-48ad-aa0e-c8db8e046c43
-- title:
--   W: poly W nondeg
-- statement:
--   The W construction uses the poly W nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachModuleLifts/WachModuleProofs/WachModuleStatementHolds.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachModuleLifts/WachModuleProofs/WachModuleStatementHolds.lean#L90-L95

import Definitions.Def_Formalism_WachModuleLifts_StatementW
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CL Formalism.CL.W
open Polynomial
variable (p : ℕ) [Fact p.Prime]

theorem Formalism.CL.W.polyW_nondeg : (polyW p).N ≠ ⊥ ∧ ¬ IsUnit (polyBase p).π₀ := by sorry
