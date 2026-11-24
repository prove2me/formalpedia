-- Prove2me | Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_mid_bound
-- name    : Formalism.NG.IdempotentNormalFormsRhoFacts.mid_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:01.242038+00:00
-- url     : https://prove2.me/theorems/a2d713a1-3f60-472a-9ebc-2ac11060c660
-- title:
--   Idempotent Normal Forms Rho Facts: mid bound
-- statement:
--   The Idempotent Normal Forms Rho Facts construction uses the mid bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L168-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthEqKerAddRange.lean#L168-L197

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsRhoFacts

theorem Formalism.NG.IdempotentNormalFormsRhoFacts.mid_bound {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type*}
    [Group G] {d : Type} [Fintype d] (ρM : Representation O G (d → KO O)) {H : Type*}
    [AddCommGroup H] [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O)
    (hcob : ∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) ≤
      (Fintype.card d : ℕ∞) * (2 * IsDiscreteValuationRing.addVal O δ) := by sorry
