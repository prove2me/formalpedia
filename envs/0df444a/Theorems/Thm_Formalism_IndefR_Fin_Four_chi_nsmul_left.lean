-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_chi_nsmul_left
-- name    : Formalism.IndefR.Fin.Four.chi_nsmul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:28.289461+00:00
-- url     : https://prove2.me/theorems/e1a0bf9d-77f2-477b-93dc-52e5ad552261
-- title:
--   Four: chi nsmul left
-- statement:
--   The Four construction uses the chi nsmul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L57-L60

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχl hχ0

theorem Formalism.IndefR.Fin.Four.chi_nsmul_left (k : ℕ) (t y : W) : χ (k • t) y = χ t y ^ k := by sorry
