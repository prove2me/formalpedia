-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LatticeSummability_latticeSummable
-- name    : Formalism.FourierDecayAlt.P.LatticeSummability.latticeSummable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:22.091912+00:00
-- url     : https://prove2.me/theorems/f70f45bf-3c74-4cf9-9f43-82957790b8e0
-- title:
--   Lattice Summability: lattice Summable
-- statement:
--   The Lattice Summability construction uses the lattice Summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean#L67-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean#L67-L151

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Finset Function
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LatticeSummability
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.LatticeSummability.latticeSummable : LatticeSummable := by sorry
