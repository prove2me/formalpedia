-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_sizesProduct_ok
-- name    : Formalism.FourierDecayAlt.P.ChainAndRowSums.sizesProduct_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:26.240723+00:00
-- url     : https://prove2.me/theorems/6707efd8-915b-42d7-bf71-f4f2c72b1c13
-- title:
--   Chain And Row Sums: sizes Product ok
-- statement:
--   The Chain And Row Sums construction uses the sizes Product ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L104-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainAndRowSums.lean#L104-L123

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

theorem Formalism.FourierDecayAlt.P.ChainAndRowSums.sizesProduct_ok : SizesProduct := by sorry
