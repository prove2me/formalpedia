-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LatticeSummability_mfac_shift
-- name    : Formalism.FourierDecayAlt.P.LatticeSummability.mfac_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:19.874333+00:00
-- url     : https://prove2.me/theorems/4e85fb1f-3242-456b-90d5-30b21f4335e3
-- title:
--   Lattice Summability: mfac shift
-- statement:
--   The Lattice Summability construction uses the mfac shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean#L32-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean#L32-L49

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

theorem Formalism.FourierDecayAlt.P.LatticeSummability.mfac_shift (K : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    mfac K L a ≤ mfac K (L + δ) (a + δ) := by sorry
