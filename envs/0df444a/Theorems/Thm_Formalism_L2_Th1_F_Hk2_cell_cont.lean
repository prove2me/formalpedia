-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_cell_cont
-- name    : Formalism.L2.Th1.F.Hk2.cell_cont
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:32.124296+00:00
-- url     : https://prove2.me/theorems/93a7674f-f4b8-46fa-aab8-5274777d0df4
-- title:
--   Hk2: cell cont
-- statement:
--   The Hk2 construction uses the cell cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L187-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L187-L193

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

theorem Formalism.L2.Th1.F.Hk2.cell_cont {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) :
    Continuous fun s : ℝ => hkCell τ s p := by sorry
