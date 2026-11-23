-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_mono
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.psd_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:14.263782+00:00
-- url     : https://prove2.me/theorems/c2a3017b-1b1e-497b-849d-c0b29319f984
-- title:
--   A1: psd mono
-- statement:
--   The A1 construction uses the psd mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L27-L43

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {α : Type}

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.psd_mono {P Q : Finset α} {k : α → α → ℂ} (hQ : Q ⊆ P) (hk : PSDOn P k) : PSDOn Q k := by sorry
