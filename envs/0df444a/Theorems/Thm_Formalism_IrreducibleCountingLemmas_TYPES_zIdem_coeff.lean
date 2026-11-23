-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_zIdem_coeff
-- name    : Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:33.998956+00:00
-- url     : https://prove2.me/theorems/8f6e4edd-5877-41b3-bdd4-00be809bcd55
-- title:
--   TYPES: z Idem coeff
-- statement:
--   The TYPES construction uses the z Idem coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean#L256-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/CentralIdempotents/GaloisConjCentralIdempotent.lean#L256-L260

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

theorem Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff [Fintype Γ] (τ : FDRep ℂ Γ) (γ : Γ) :
    (zIdem τ).coeff γ = (Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹) := by sorry
