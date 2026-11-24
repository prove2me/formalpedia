-- Prove2me | Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_eq_zero_of_gens
-- name    : Formalism.NG.ColumnGeneratorDecomposition.eq_zero_of_gens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:38.29999+00:00
-- url     : https://prove2.me/theorems/498ffa0c-6530-4bcf-b98e-63f52122bfe2
-- title:
--   Column Generator Decomposition: eq zero of gens
-- statement:
--   The Column Generator Decomposition construction uses the eq zero of gens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L67-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L67-L87

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
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
open Formalism.NG.ColumnGeneratorDecomposition
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
variable {M : Type*} [AddCommGroup M] [Module A M]

theorem Formalism.NG.ColumnGeneratorDecomposition.eq_zero_of_gens [Fintype ι] {e₁ : A} {δ : T'} {D : ι → Subgroup G}
    {Kc : ∀ l, Fin (j l) → G → A} {k0 : ι → G → A}
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M)
    (hY : ∀ y : Ymod r χ E, φ (Submodule.Quotient.mk ((y, 0) : ColFreeJ A r χ E ι j)) = 0)
    (hν : ∀ l, φ (Submodule.Quotient.mk (fNu l)) = 0)
    (hσ : ∀ l a, φ (Submodule.Quotient.mk (fSig l a)) = 0)
    (hσ₀ : ∀ l, φ (Submodule.Quotient.mk (fSig0 l)) = 0) : φ = 0 := by sorry
