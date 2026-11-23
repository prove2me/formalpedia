-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_Sqf_coeff_monicOf_lt
-- name    : Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:33.011793+00:00
-- url     : https://prove2.me/theorems/a5319480-0cd2-4b90-86a6-775ec5a779ac
-- title:
--   Sqf: coeff monic Of lt
-- statement:
--   The Sqf construction uses the coeff monic Of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L13-L19

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

theorem Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by sorry
