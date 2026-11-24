-- Prove2me | Theorems.Thm_Formalism_NG_blockRhoLat
-- name    : Formalism.NG.blockRhoLat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:22.465842+00:00
-- url     : https://prove2.me/theorems/ce56466b-c01e-42e5-b363-fc606d6d6f9a
-- title:
--   NG: block Rho Lat
-- statement:
--   The NG construction uses the block Rho Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L103-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CharacterColumnKernelsOfBlockChiCOfBlockChiOne.lean#L103-L147

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
set_option maxHeartbeats 4000000

theorem Formalism.NG.blockRhoLat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ : ℕ) (sE : Finset G) (tE : G → T'),
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : LatQ O d ρ, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ m : LatQ O d ρ, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (LatQ O d ρ) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → (LatQ O d ρ)),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (LatQ O d ρ) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (what₂ : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (lenRow : ι' → ℕ∞)
      (Q : Submodule O (H1z ρM)) (s : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card d
    let h0 : ι' → ℕ∞ := fun w => Module.length O (LinearMap.ker (colDO (O := O) (M := LatQ O d ρ) r χ (D w)))
    (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ := by sorry
