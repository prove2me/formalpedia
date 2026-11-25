-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_SSPh_sum_ind
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh.sum_ind
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:34:22.360716+00:00
-- url     : https://prove2.me/theorems/c891f231-0f08-5fb9-9a88-ddbaa6583322
-- title:
--   SSPh: sum ind
-- statement:
--   The SSPh construction uses the sum ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSPhaseA.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTSSPhaseA.lean#L10-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSPhaseA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh.sum_ind (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ i : Fin (P.k - 1), (if (i : ℕ) + 1 = l then 1 else 0) = 1 := by sorry
