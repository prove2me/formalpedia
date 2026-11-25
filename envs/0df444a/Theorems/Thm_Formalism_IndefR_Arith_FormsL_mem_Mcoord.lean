-- Prove2me | Theorems.Thm_Formalism_IndefR_Arith_FormsL_mem_Mcoord
-- name    : Formalism.IndefR.Arith.FormsL.mem_Mcoord
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:32.872941+00:00
-- url     : https://prove2.me/theorems/dd233efd-5a05-5a65-8f21-e7fcdd2ef3a9
-- title:
--   Forms L: mem Mcoord
-- statement:
--   The Forms L construction uses the mem Mcoord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L155-L157

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

theorem Formalism.IndefR.Arith.FormsL.mem_Mcoord (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {d : ℕ} (b : Fin d → WL)
    (c : Fin d → LL) : c ∈ A.Mcoord J0 lam0 eC b ↔ ∑ i, c i • b i ∈ A.Mj J0 lam0 eC := by sorry
