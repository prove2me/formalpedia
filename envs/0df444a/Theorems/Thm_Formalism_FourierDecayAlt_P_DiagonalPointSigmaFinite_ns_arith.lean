-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_arith
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:28.822515+00:00
-- url     : https://prove2.me/theorems/9191f56b-795f-473e-87a4-510953372724
-- title:
--   Diagonal Point Sigma Finite: ns arith
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L286-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L286-L311

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_arith (m C₉ q ny : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hkey : ε * (((m : ℝ) + 2) * ((C₉ : ℝ) + 1)) ≤ 1 / 2) (hε2s : ε * ((m : ℝ) + 2) ≤ 1 / 2)
    (hq : q = 4 * m + 12) (hnyle : (ny : ℝ) ≤ ((m : ℝ) + 2) ^ 2) :
    ε * (((m + 2) * C₉ + (m + 2) * (C₉ + 1) * q + 2 * (m + 1) + 2 * ny : ℕ) : ℝ) +
      ((m + 2 : ℕ) : ℝ) ≤ (q : ℝ) := by sorry
