-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_block_diagonal_psd
-- name    : Formalism.FourierDecayAlt.P.block_diagonal_psd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:29:07.417883+00:00
-- url     : https://prove2.me/theorems/c8be4e94-2e65-404a-bf8d-6f220b222c95
-- title:
--   P: block diagonal psd
-- statement:
--   The P construction uses the block diagonal psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PullLatticeTypedUnit.lean#L194-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PullLatticeTypedUnit.lean#L194-L231

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.block_diagonal_psd : Formalism.FourierDecayAlt.J.BlockDiagPSD := by sorry
