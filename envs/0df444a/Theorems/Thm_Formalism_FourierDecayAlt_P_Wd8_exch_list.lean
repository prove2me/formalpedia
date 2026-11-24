-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_exch_list
-- name    : Formalism.FourierDecayAlt.P.Wd8.exch_list
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:02.425004+00:00
-- url     : https://prove2.me/theorems/46b021d7-8a99-46b4-a69d-33e4f442d65b
-- title:
--   Wd8: exch list
-- statement:
--   The Wd8 construction uses the exch list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L13-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L13-L45

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

theorem Formalism.FourierDecayAlt.P.Wd8.exch_list (X : R) (f g : ι → R) (L : List ι)
    (h1 : ∀ σ ∈ L, X * f σ * g σ = g σ * f σ * X)
    (h2 : L.Pairwise fun σ τ => Commute (f τ) (g σ) ∧ Commute (f σ) (g τ)) :
    X * (L.map f).prod * (L.map g).prod = (L.map g).prod * (L.map f).prod * X := by sorry
