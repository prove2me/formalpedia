-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_cell_bound
-- name    : Formalism.L2.Th1.F.Hk2.cell_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:49.623964+00:00
-- url     : https://prove2.me/theorems/8026cbf6-34ff-4564-a0e1-f7c67f848e13
-- title:
--   Hk2: cell bound
-- statement:
--   The Hk2 construction uses the cell bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L195-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L195-L226

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

theorem Formalism.L2.Th1.F.Hk2.cell_bound {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖hkCell τ s p‖ ≤ 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹ := by sorry
