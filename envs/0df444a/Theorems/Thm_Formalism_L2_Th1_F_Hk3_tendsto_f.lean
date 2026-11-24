-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Hk3_tendsto_f
-- name    : Formalism.L2.Th1.F.Hk3.tendsto_f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:30.15295+00:00
-- url     : https://prove2.me/theorems/2fcf681e-d574-485a-9359-8a754e830636
-- title:
--   Hk3: tendsto f
-- statement:
--   The Hk3 construction uses the tendsto f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelLineZero.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HeckeKernelLineZero.lean#L33-L37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
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

theorem Formalism.L2.Th1.F.Hk3.tendsto_f {a : ℝ} (ha : 1 / 2 < a) {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => 1 + t ^ 2) l atTop) :
    Tendsto (fun t : ℝ => t * (1 + t ^ 2) ^ (-a)) l (𝓝 0) := by sorry
