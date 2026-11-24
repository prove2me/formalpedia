-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_pt_ne_zero
-- name    : Formalism.L2.Th1.F.Hk2.pt_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:30:29.417803+00:00
-- url     : https://prove2.me/theorems/34247e46-48cf-4257-a682-6a05d92b2ffc
-- title:
--   Hk2: pt ne zero
-- statement:
--   The Hk2 construction uses the pt ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L168-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L168-L175

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2

theorem Formalism.L2.Th1.F.Hk2.pt_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) (m : ℤ) (x : ℝ) :
    (m : ℂ) + (x : ℂ) + (n : ℂ) * τ ≠ 0 := by sorry
