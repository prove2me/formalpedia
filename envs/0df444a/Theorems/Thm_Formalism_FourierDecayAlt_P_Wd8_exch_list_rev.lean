-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exch_list_rev
-- name    : Formalism.FourierDecayAlt.P.Wd8.exch_list_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:57.201806+00:00
-- url     : https://prove2.me/theorems/3efabc72-38df-4fd3-984a-69ee371a6ad3
-- title:
--   Wd8: exch list rev
-- statement:
--   The Wd8 construction uses the exch list rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L47-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L47-L79

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

theorem Formalism.FourierDecayAlt.P.Wd8.exch_list_rev (X : R) (f g : ι → R) (L : List ι)
    (h1 : ∀ σ ∈ L, f σ * X * g σ = g σ * X * f σ)
    (h2 : L.Pairwise fun σ τ => Commute (f τ) (g σ) ∧ Commute (f σ) (g τ)) :
    (L.reverse.map f).prod * X * (L.map g).prod = (L.map g).prod * X * (L.reverse.map f).prod := by sorry
