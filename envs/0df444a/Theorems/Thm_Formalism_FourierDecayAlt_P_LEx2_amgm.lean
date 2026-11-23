-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_amgm
-- name    : Formalism.FourierDecayAlt.P.LEx2.amgm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:59.798873+00:00
-- url     : https://prove2.me/theorems/b1072003-2c41-4f34-af68-eaa4fab91636
-- title:
--   LEx2: amgm
-- statement:
--   The LEx2 construction uses the amgm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L515-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean#L515-L519

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx2.amgm (a b δ : ℝ) (hδ : 0 < δ) : a * b ≤ (a ^ 2 / δ + δ * b ^ 2) / 2 := by sorry
