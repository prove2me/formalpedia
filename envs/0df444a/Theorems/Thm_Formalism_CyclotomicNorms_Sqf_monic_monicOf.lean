-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_Sqf_monic_monicOf
-- name    : Formalism.CyclotomicNorms.Sqf.monic_monicOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:35.398243+00:00
-- url     : https://prove2.me/theorems/0fe75b58-cd0b-48c1-904d-112a7bfba1a5
-- title:
--   Sqf: monic monic Of
-- statement:
--   The Sqf construction uses the monic monic Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L32-L34

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

theorem Formalism.CyclotomicNorms.Sqf.monic_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by sorry
