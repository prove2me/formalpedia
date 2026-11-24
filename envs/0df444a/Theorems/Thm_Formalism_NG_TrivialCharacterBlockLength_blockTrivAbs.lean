-- Prove2me | Theorems.Thm_Formalism_NG_TrivialCharacterBlockLength_blockTrivAbs
-- name    : Formalism.NG.TrivialCharacterBlockLength.blockTrivAbs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:46.166436+00:00
-- url     : https://prove2.me/theorems/9a3b3061-4927-4634-9d80-57dbfdb8747b
-- title:
--   Trivial Character Block Length: block Triv Abs
-- statement:
--   The Trivial Character Block Length construction uses the block Triv Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean#L35-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean#L35-L87

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
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
open Formalism.NG.TrivialCharacterBlockLength

theorem Formalism.NG.TrivialCharacterBlockLength.blockTrivAbs {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
    {H : Type*} [AddCommGroup H] [Module O H]
    (ρM : Representation O G M) (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM)
    {ι : Type*} [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
    (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
    (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞)
    (hrows : ∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))),
      F w ≤ A ∧ Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A)
    (hcols : ∀ w ∈ cols, ∀ h : H,
      resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w)
    (hQ : ∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q)
    (hsel : Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols,
      (F w).comap (resH1 ρM (D w))) ≤ s) :
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) + (s + ∑ w ∈ what₂, lenRow w) := by sorry
