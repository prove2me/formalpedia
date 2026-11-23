-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_rpow_decay_arith
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.rpow_decay_arith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:56.924992+00:00
-- url     : https://prove2.me/theorems/54cd688f-8790-493a-9fe6-443931da99f0
-- title:
--   Diagonal Point Sigma Finite: rpow decay arith
-- statement:
--   The Diagonal Point Sigma Finite construction uses the rpow decay arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L232-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L232-L235

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.rpow_decay_arith {τ ε : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (q N p : ℕ)
    (h : ε * (N : ℝ) + (p : ℝ) ≤ (q : ℝ)) : τ ^ q * (τ ^ (-ε)) ^ N ≤ τ ^ p := by sorry
