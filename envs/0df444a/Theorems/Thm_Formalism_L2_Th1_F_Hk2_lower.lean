-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_lower
-- name    : Formalism.L2.Th1.F.Hk2.lower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:46.060695+00:00
-- url     : https://prove2.me/theorems/6ba89b7e-2d48-4c05-81ec-fc63c115f75e
-- title:
--   Hk2: lower
-- statement:
--   The Hk2 construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L112-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L112-L141

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

theorem Formalism.L2.Th1.F.Hk2.lower {τ : ℂ} (m n : ℤ) (hn : n ≠ 0) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    kap τ * (|(m : ℝ)| + |(n : ℝ)|) ≤ ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ := by sorry
