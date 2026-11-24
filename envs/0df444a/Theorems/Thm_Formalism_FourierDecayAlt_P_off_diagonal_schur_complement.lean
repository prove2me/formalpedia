-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_off_diagonal_schur_complement
-- name    : Formalism.FourierDecayAlt.P.off_diagonal_schur_complement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:58.133495+00:00
-- url     : https://prove2.me/theorems/1f78b2d0-35b3-429f-97e6-13e973043b90
-- title:
--   P: off diagonal schur complement
-- statement:
--   The P construction uses the off diagonal schur complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L132-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L132-L276

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.TA2

theorem Formalism.FourierDecayAlt.P.off_diagonal_schur_complement : Formalism.FourierDecayAlt.TA.OffDiagSchur := by sorry
