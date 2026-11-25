-- Prove2me | Theorems.Thm_Formalism_IndefR_LiftF_IsIo_unique
-- name    : Formalism.IndefR.LiftF.IsIo.unique
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:43:18.429867+00:00
-- url     : https://prove2.me/theorems/1a794df7-c109-49b6-9f4d-835339d92c47
-- title:
--   Is Io: unique
-- statement:
--   The Is Io construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L46-L56

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
variable {G H S Sinf Ds Dt : Type*} [MeasurableSpace H]
  [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]

theorem Formalism.IndefR.LiftF.IsIo.unique {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {pt : Sinf → S}
    {T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))}
    {CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))} {io io' : CCs →ₗ[ℂ] CCt}
    (hT : ∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0)
    (h : IsIo ν 𝓕 th pt T CCs CCt io) (h' : IsIo ν 𝓕 th pt T CCs CCt io') : io = io' := by sorry
