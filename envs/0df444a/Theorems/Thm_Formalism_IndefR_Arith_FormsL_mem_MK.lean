-- Prove2me | Theorems.Thm_Formalism_IndefR_Arith_FormsL_mem_MK
-- name    : Formalism.IndefR.Arith.FormsL.mem_MK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:07.692026+00:00
-- url     : https://prove2.me/theorems/839d4020-9230-4535-97c3-6e283e2b6198
-- title:
--   Forms L: mem MK
-- statement:
--   The Forms L construction uses the mem MK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L137-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean#L137-L137

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

theorem Formalism.IndefR.Arith.FormsL.mem_MK {f : WL} : f ∈ A.MK ↔ ∃ h : f ∈ A.WK, ∀ lp (y : A.Pt lp), A.nrm lp y ⟨f, h⟩ ≤ 1 := by sorry
