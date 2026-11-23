-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_isUnit_det_swap
-- name    : Formalism.CyclotomicNorms.residueMatrixData.isUnit_det_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:12.981606+00:00
-- url     : https://prove2.me/theorems/7353fe22-6426-4d1b-a344-1eb301e2fbed
-- title:
--   residue Matrix Data: is Unit det swap
-- statement:
--   The residue Matrix Data construction uses the is Unit det swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L65-L66

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {R : Type*} [CommRing R]

theorem Formalism.CyclotomicNorms.residueMatrixData.isUnit_det_swap {a : ℕ} (i j : Fin a) : IsUnit (Matrix.swap R i j).det := by sorry
