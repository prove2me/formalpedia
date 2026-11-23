-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_volume_unitary
-- name    : Formalism.FourierDecayAlt.P.G8.volume_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:36.185263+00:00
-- url     : https://prove2.me/theorems/84709bb5-8409-4c49-aec9-504072a19a3d
-- title:
--   G8: volume unitary
-- statement:
--   The G8 construction uses the volume unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L24-L34

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8

theorem Formalism.FourierDecayAlt.P.G8.volume_unitary (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Measure.map (fun x : Fin d → ℂ => W *ᵥ x) (volume : Measure (Fin d → ℂ)) = volume := by sorry
