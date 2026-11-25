-- Prove2me | Theorems.Thm_Formalism_IndefR_LiftF_IsKap_unique
-- name    : Formalism.IndefR.LiftF.IsKap.unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:09.47856+00:00
-- url     : https://prove2.me/theorems/b31246ca-1ce5-4b91-a684-9f02fec7514d
-- title:
--   Is Kap: unique
-- statement:
--   The Is Kap construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L186-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HasInfExpF.lean#L186-L197

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
variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem Formalism.IndefR.LiftF.IsKap.unique {Tup Sig : Type*} {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam : Tup → ℕ → Sig → ℝ} {κ κ' : ℝ} (h : IsKap m dnup partE lam κ) (h' : IsKap m dnup partE lam κ')
    (μ : Tup) (σ : Sig) (hσ : partE σ ≠ ⊥) (hl : ∏ j ∈ Finset.Icc 1 m, lam μ j σ ≠ 0) : κ = κ' := by sorry
