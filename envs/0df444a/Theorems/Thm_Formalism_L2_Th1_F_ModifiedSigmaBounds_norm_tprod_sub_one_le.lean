-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_norm_tprod_sub_one_le
-- name    : Formalism.L2.Th1.F.ModifiedSigmaBounds.norm_tprod_sub_one_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:21.206712+00:00
-- url     : https://prove2.me/theorems/805c2d54-cfc4-47ef-bff6-f9ba637933d6
-- title:
--   Modified Sigma Bounds: norm tprod sub one le
-- statement:
--   The Modified Sigma Bounds construction uses the norm tprod sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L91-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L91-L114

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
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
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
open Formalism.L2.Th1.F.ModifiedSigmaBounds
open SigmaConv

theorem Formalism.L2.Th1.F.ModifiedSigmaBounds.norm_tprod_sub_one_le (hs : SigmaSummable) (L : PeriodPair) (z : ℂ)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖) :
    ‖∏' l : L.lattice, wFactor (l : ℂ) z - 1‖
      ≤ Real.exp (∑' l : L.lattice, 2 * ‖z‖ ^ 3 * ‖l‖ ^ (-3 : ℝ)) - 1 := by sorry
