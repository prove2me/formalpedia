-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaConv_summable_majorant
-- name    : Formalism.L2.Th1.F.SigmaConv.summable_majorant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:25.170088+00:00
-- url     : https://prove2.me/theorems/fe310d27-e446-4bd6-9170-cb57cc02db83
-- title:
--   Sigma Conv: summable majorant
-- statement:
--   The Sigma Conv construction uses the summable majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaConv.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaConv.lean#L87-L89

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
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
open Formalism.L2.Th1.F.SigmaConv

theorem Formalism.L2.Th1.F.SigmaConv.summable_majorant (L : PeriodPair) (r : ℝ) :
    Summable (fun l : L.lattice => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ)) := by sorry
