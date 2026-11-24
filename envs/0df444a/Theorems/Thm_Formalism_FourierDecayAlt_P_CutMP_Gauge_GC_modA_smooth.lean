-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_modA_smooth
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.modA_smooth
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:15.950629+00:00
-- url     : https://prove2.me/theorems/da28a0de-9b9d-41b4-8c57-c86d087f6799
-- title:
--   GC: mod A smooth
-- statement:
--   The GC construction uses the mod A smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/cut_GCore_GTConnCut.lean#L104-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/cut_GCore_GTConnCut.lean#L104-L124

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGenTransferCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.modA_smooth (P : M.Par) (ρ : M.Ty P) (hTT : 0 ≤ P.TT) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by sorry
