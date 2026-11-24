-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_eventually_small
-- name    : Formalism.L2.Th1.F.ModifiedSigmaBounds.eventually_small
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:34.496346+00:00
-- url     : https://prove2.me/theorems/2b5e69f2-39fd-4103-a5a7-9c5cf54bc67c
-- title:
--   Modified Sigma Bounds: eventually small
-- statement:
--   The Modified Sigma Bounds construction uses the eventually small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L72-L89

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

theorem Formalism.L2.Th1.F.ModifiedSigmaBounds.eventually_small (L : PeriodPair) :
    ∀ᶠ z : ℂ in nhds 0, ∀ l : L.lattice, (l : ℂ) ≠ 0 → 2 * ‖z‖ ≤ ‖(l : ℂ)‖ := by sorry
