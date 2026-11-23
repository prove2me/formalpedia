-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_prod_mul_list
-- name    : Formalism.FourierDecayAlt.P.Wd8.prod_mul_list
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:20.734182+00:00
-- url     : https://prove2.me/theorems/f876fd91-0ae7-4748-8bdb-9cbf2ca409d2
-- title:
--   Wd8: prod mul list
-- statement:
--   The Wd8 construction uses the prod mul list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L81-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L81-L99

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {R ι : Type} [Monoid R]

theorem Formalism.FourierDecayAlt.P.Wd8.prod_mul_list (x y : ι → R) (L : List ι)
    (h2 : L.Pairwise fun σ τ => Commute (y σ) (x τ)) :
    (L.map fun σ => x σ * y σ).prod = (L.map x).prod * (L.map y).prod := by sorry
