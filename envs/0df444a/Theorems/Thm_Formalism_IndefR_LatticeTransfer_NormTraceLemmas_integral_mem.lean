-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_NormTraceLemmas_integral_mem
-- name    : Formalism.IndefR.LatticeTransfer.NormTraceLemmas.integral_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:10.712872+00:00
-- url     : https://prove2.me/theorems/0d9d0907-f249-43eb-a131-e8cfcde92609
-- title:
--   Norm Trace Lemmas: integral mem
-- statement:
--   The Norm Trace Lemmas construction uses the integral mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/ExistsStrictHenselianAbsolutelyClosedLocalRing.lean#L93-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/ExistsStrictHenselianAbsolutelyClosedLocalRing.lean#L93-L117

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
variable [NumberField K]

theorem Formalism.IndefR.LatticeTransfer.NormTraceLemmas.integral_mem (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) :
    (Fintype.card G : K) ^ 2 * LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) ∈
      integralClosure ℤ K := by sorry
