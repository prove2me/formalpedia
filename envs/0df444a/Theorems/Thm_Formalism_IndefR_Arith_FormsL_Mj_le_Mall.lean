-- Prove2me | Theorems.Thm_Formalism_IndefR_Arith_FormsL_Mj_le_Mall
-- name    : Formalism.IndefR.Arith.FormsL.Mj_le_Mall
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:55.781509+00:00
-- url     : https://prove2.me/theorems/67dccd5e-98b4-4da2-a175-a51fb70a7dc5
-- title:
--   Forms L: Mj le Mall
-- statement:
--   The Forms L construction uses the Mj le Mall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L148-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L148-L149

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

theorem Formalism.IndefR.Arith.FormsL.Mj_le_Mall (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    A.Mj J0 lam0 eC ≤ A.Mall J0 lam0 := by sorry
