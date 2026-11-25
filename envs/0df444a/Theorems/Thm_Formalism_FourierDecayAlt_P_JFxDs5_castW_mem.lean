-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_castW_mem
-- name    : Formalism.FourierDecayAlt.P.JFxDs5.castW_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:03.342237+00:00
-- url     : https://prove2.me/theorems/2a866785-01d8-5d90-aaa6-0d1e2e741cee
-- title:
--   JFx Ds5: cast W mem
-- statement:
--   The JFx Ds5 construction uses the cast W mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean#L41-L43

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxDs5.castW_mem {μ : B.Mat k 0} (hμ : μ ∈ GV k 0) : (castW μ)ᴴ * Hb k * castW μ = Hb k := by sorry
