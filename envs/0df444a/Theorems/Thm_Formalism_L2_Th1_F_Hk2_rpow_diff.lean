-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk2_rpow_diff
-- name    : Formalism.L2.Th1.F.Hk2.rpow_diff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:30:21.918609+00:00
-- url     : https://prove2.me/theorems/114b4bbb-ed78-48b1-b814-25b15575d162
-- title:
--   Hk2: rpow diff
-- statement:
--   The Hk2 construction uses the rpow diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelCellContinuous.lean#L16-L36

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb

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

theorem Formalism.L2.Th1.F.Hk2.rpow_diff {κ ρ a b t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (ha : ρ ≤ a) (hb : ρ ≤ b)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |a ^ (-t) - b ^ (-t)| ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ * |a - b| := by sorry
