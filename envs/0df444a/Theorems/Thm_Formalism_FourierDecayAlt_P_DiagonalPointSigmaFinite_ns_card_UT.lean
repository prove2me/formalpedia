-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_card_UT
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_card_UT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:21.311222+00:00
-- url     : https://prove2.me/theorems/ea27e078-b8a6-47f6-8817-8e80a7b14fec
-- title:
--   Diagonal Point Sigma Finite: ns card UT
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns card UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L237-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L237-L239

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_card_UT (d : ℕ) : Fintype.card (UT d) ≤ d ^ 2 := by sorry
