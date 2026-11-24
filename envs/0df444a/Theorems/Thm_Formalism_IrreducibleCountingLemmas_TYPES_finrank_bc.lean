-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_finrank_bc
-- name    : Formalism.IrreducibleCountingLemmas.TYPES.finrank_bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:21.289719+00:00
-- url     : https://prove2.me/theorems/23a76347-0bf4-4f34-b938-1b2e1c5bd948
-- title:
--   TYPES: finrank bc
-- statement:
--   The TYPES construction uses the finrank bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean#L252-L254

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]

theorem Formalism.IrreducibleCountingLemmas.TYPES.finrank_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) :
    Module.finrank ℂ (bc σ τ) = Module.finrank ℂ τ := by sorry
