-- Prove2me | Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_finsum_le
-- name    : Formalism.LT.InverseIntegralClassesKeyFacts.norm_finsum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:05.715717+00:00
-- url     : https://prove2.me/theorems/0f76ce38-adc3-492a-a5f0-14375d0d197b
-- title:
--   Inverse Integral Classes Key Facts: norm finsum le
-- statement:
--   The Inverse Integral Classes Key Facts construction uses the norm finsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L17-L24

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT
open Formalism.G
open Formalism.LT.InverseIntegralClassesKeyFacts
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.InverseIntegralClassesKeyFacts.norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by sorry
