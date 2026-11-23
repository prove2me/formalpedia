-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_measurable_mulVec
-- name    : Formalism.FourierDecayAlt.P.G8.measurable_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:22.744798+00:00
-- url     : https://prove2.me/theorems/661ace30-9040-4aec-a597-e6b9900f0b5d
-- title:
--   G8: measurable mul Vec
-- statement:
--   The G8 construction uses the measurable mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L36-L39

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

theorem Formalism.FourierDecayAlt.P.G8.measurable_mulVec (d : ℕ) (W : Matrix (Fin d) (Fin d) ℂ) :
    Measurable (fun x : Fin d → ℂ => W *ᵥ x) := by sorry
