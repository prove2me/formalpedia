-- Prove2me | Theorems.Thm_Formalism_IndefR_LiftF_IsThetaP_unique
-- name    : Formalism.IndefR.LiftF.IsThetaP.unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:13.938346+00:00
-- url     : https://prove2.me/theorems/212d430c-6bec-4c4e-b338-ff324a0f51a8
-- title:
--   Is Theta P: unique
-- statement:
--   The Is Theta P construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L148-L153

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

theorem Formalism.IndefR.LiftF.IsThetaP.unique {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf' → S'}
    {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf'} {A : Submodule ℂ (H' → Tau)}
    {thP thP' : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))}
    (h : IsThetaP ν 𝓕 th pt io A thP) (h' : IsThetaP ν 𝓕 th pt io A thP') : thP = thP' := by sorry
