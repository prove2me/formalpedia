-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_trace_eS
-- name    : Formalism.IndefR.LatticeTransfer.IdempotentLemmas.trace_eS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:14.884808+00:00
-- url     : https://prove2.me/theorems/88fc0e77-570d-419d-960e-2bea4902c174
-- title:
--   Idempotent Lemmas: trace e S
-- statement:
--   The Idempotent Lemmas construction uses the trace e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L72-L81

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

theorem Formalism.IndefR.LatticeTransfer.IdempotentLemmas.trace_eS {T U : Type} [AddCommGroup T] [Module K T] [AddCommGroup U] [Module K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    LinearMap.trace K U (eS τ σ) =
      charOf τ 1 / (Fintype.card G : K) * ∑ x : G, charOf τ x⁻¹ * charOf σ x := by sorry
