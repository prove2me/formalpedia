-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_Sqf_natDegree_monicOf
-- name    : Formalism.CyclotomicNorms.Sqf.natDegree_monicOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:44.203492+00:00
-- url     : https://prove2.me/theorems/f01def9a-756b-45f1-be35-13d95c6a4612
-- title:
--   Sqf: nat Degree monic Of
-- statement:
--   The Sqf construction uses the nat Degree monic Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L28-L30

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]

theorem Formalism.CyclotomicNorms.Sqf.natDegree_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by sorry
