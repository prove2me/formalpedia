-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk4_cellOff_norm_le
-- name    : Formalism.L2.Th1.F.Hk4.cellOff_norm_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:35.60663+00:00
-- url     : https://prove2.me/theorems/9ea1260f-01a5-483a-aabb-551a19089477
-- title:
--   Hk4: cell Off norm le
-- statement:
--   The Hk4 construction uses the cell Off norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean#L16-L22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk4

theorem Formalism.L2.Th1.F.Hk4.cellOff_norm_le {τ : ℂ} {b : ℤ × ℤ → ℝ}
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (p : ℤ × ℤ) : ‖cellOff τ s p‖ ≤ |b p| := by sorry
