-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_fderiv
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_fderiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:45.213219+00:00
-- url     : https://prove2.me/theorems/838c0917-2bcc-44af-bbe6-03a65e172646
-- title:
--   GC: jet T fderiv
-- statement:
--   The GC construction uses the jet T fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L68-L72

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_fderiv {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {g₀ : D} {i : ℕ} (h : iteratedFDeriv ℝ (i + 1) F g₀ = 0) :
    iteratedFDeriv ℝ i (fderiv ℝ F) g₀ = 0 := by sorry
