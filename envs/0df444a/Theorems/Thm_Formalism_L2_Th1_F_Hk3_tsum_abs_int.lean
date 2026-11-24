-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk3_tsum_abs_int
-- name    : Formalism.L2.Th1.F.Hk3.tsum_abs_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:33:08.37581+00:00
-- url     : https://prove2.me/theorems/c3bdc51e-b36e-42bb-97cf-6fe47d7318d6
-- title:
--   Hk3: tsum abs int
-- statement:
--   The Hk3 construction uses the tsum abs int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelLineZero.lean#L147-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelLineZero.lean#L147-L160

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
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
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk3

theorem Formalism.L2.Th1.F.Hk3.tsum_abs_int {b : ℝ} (hb : 1 < b) :
    ∑' n : ℤ, |(n : ℝ)| ^ (-b) = 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ b := by sorry
