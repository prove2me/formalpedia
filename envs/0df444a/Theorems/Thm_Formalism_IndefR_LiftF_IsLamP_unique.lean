-- Prove2me | Theorems.Thm_Formalism_IndefR_LiftF_IsLamP_unique
-- name    : Formalism.IndefR.LiftF.IsLamP.unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:51.206367+00:00
-- url     : https://prove2.me/theorems/2bd5aa3b-9fc3-5b30-b786-3443e079a818
-- title:
--   Is Lam P: unique
-- statement:
--   The Is Lam P construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L167-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L167-L174

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.IndefR Formalism.IndefR.LiftF
variable {G' H' S' Sinf' TK Tau : Type*} [MeasurableSpace H']
  [AddCommGroup Sinf'] [Module ℂ Sinf'] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
variable {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]

theorem Formalism.IndefR.LiftF.IsLamP.unique {Sig : Type*} {thW : A →ₗ[ℂ] Amb} {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb}
    {lam lam' : Sig → ℝ} (h : IsLamP thW adj part lam) (h' : IsLamP thW adj part lam') {σ : Sig}
    (hσ : part σ ≠ ⊥) : lam σ = lam' σ := by sorry
