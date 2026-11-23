-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_mul_rho
-- name    : Formalism.IndefR.LatticeTransfer.IdempotentLemmas.eS_mul_rho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:38.487536+00:00
-- url     : https://prove2.me/theorems/77cbc5bd-ee6b-465f-af60-47e3b74e93e5
-- title:
--   Idempotent Lemmas: e S mul rho
-- statement:
--   The Idempotent Lemmas construction uses the e S mul rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L30-L37

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

theorem Formalism.IndefR.LatticeTransfer.IdempotentLemmas.eS_mul_rho {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (y : G) :
    eS τ ρ * ρ y = (charOf τ 1 / (Fintype.card G : K)) • ∑ g : G, charOf τ (y * g⁻¹) • ρ g := by sorry
