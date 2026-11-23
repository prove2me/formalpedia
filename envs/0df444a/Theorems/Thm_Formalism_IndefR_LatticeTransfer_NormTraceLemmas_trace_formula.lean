-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_NormTraceLemmas_trace_formula
-- name    : Formalism.IndefR.LatticeTransfer.NormTraceLemmas.trace_formula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:39.144918+00:00
-- url     : https://prove2.me/theorems/b7d49778-a5cc-44b1-9980-9bf62bc9bff9
-- title:
--   Norm Trace Lemmas: trace formula
-- statement:
--   The Norm Trace Lemmas construction uses the trace formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/ExistsStrictHenselianAbsolutelyClosedLocalRing.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/ExistsStrictHenselianAbsolutelyClosedLocalRing.lean#L40-L51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
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
open Formalism.IndefR.LatticeTransfer.NormTraceLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
open Classical

theorem Formalism.IndefR.LatticeTransfer.NormTraceLemmas.trace_formula (τ : Representation K G T) (H₀ H : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (χ : H →* (𝓞 K)ˣ) (a b : G) :
    LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) =
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹) *
        ∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b) := by sorry
