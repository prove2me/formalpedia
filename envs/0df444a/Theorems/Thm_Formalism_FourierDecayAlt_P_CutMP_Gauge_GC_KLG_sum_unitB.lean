-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLG_sum_unitB
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG.sum_unitB
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:47.034062+00:00
-- url     : https://prove2.me/theorems/0459dd0d-1d24-522e-b0cc-8ff4da0c226d
-- title:
--   KLG: sum unit B
-- statement:
--   The KLG construction uses the sum unit B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLLieGrpGeo.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLLieGrpGeo.lean#L22-L46

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLLieGrpGeo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG.sum_unitB {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    colM Bs * B * ((colM Bs)ᴴ * Hpk k r) = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := by sorry
