-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_charOf_conj
-- name    : Formalism.IndefR.LatticeTransfer.IdempotentLemmas.charOf_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:17.326631+00:00
-- url     : https://prove2.me/theorems/5b0c7906-252d-4950-b19f-2b0d3df8999d
-- title:
--   Idempotent Lemmas: char Of conj
-- statement:
--   The Idempotent Lemmas construction uses the char Of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L16-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem Formalism.IndefR.LatticeTransfer.IdempotentLemmas.charOf_conj {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (g h : G) : charOf τ (h * g * h⁻¹) = charOf τ g := by sorry
