-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LatticeSummability_mfac_anti
-- name    : Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:12.554109+00:00
-- url     : https://prove2.me/theorems/effdd737-606d-4c91-bcb7-9e80f0452553
-- title:
--   Lattice Summability: mfac anti
-- statement:
--   The Lattice Summability construction uses the mfac anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean#L18-L30

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

theorem Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti (K : ℕ) {L : ℝ} (hL : 0 < L) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    mfac K L b' ≤ mfac K L b := by sorry
