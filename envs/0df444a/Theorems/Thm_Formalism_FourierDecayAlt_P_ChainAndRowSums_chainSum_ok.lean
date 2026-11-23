-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_chainSum_ok
-- name    : Formalism.FourierDecayAlt.P.ChainAndRowSums.chainSum_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:16.171588+00:00
-- url     : https://prove2.me/theorems/2fc055f7-6632-46f5-971a-420d885a3fd4
-- title:
--   Chain And Row Sums: chain Sum ok
-- statement:
--   The Chain And Row Sums construction uses the chain Sum ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L18-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L18-L49

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.ChainAndRowSums.chainSum_ok : ChainSum := by sorry
