-- Prove2me | Theorems.Thm_Formalism_IndefR_Arith_FormsL_pet_conj_symm
-- name    : Formalism.IndefR.Arith.FormsL.pet_conj_symm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:59.60815+00:00
-- url     : https://prove2.me/theorems/1bcb8f36-4dfa-43ce-93d3-ca1b4ab16f70
-- title:
--   Forms L: pet conj symm
-- statement:
--   The Forms L construction uses the pet conj symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L115-L116

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open scoped InnerProductSpace Matrix
open Formalism Formalism.IndefR Formalism.IndefR.Arith
variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)
open Formalism.IndefR.Arith.FormsL

theorem Formalism.IndefR.Arith.FormsL.pet_conj_symm (σ : LL →+* ℂ) (x y : WL) : A.pet σ y x = starRingEnd ℂ (A.pet σ x y) := by sorry
