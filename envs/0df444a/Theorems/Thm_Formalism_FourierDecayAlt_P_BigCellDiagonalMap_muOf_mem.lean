-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_muOf_mem
-- name    : Formalism.FourierDecayAlt.P.BigCellDiagonalMap.muOf_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:02.352811+00:00
-- url     : https://prove2.me/theorems/5d5cab0a-13fa-4769-8103-26c147c9a051
-- title:
--   Big Cell Diagonal Map: mu Of mem
-- statement:
--   The Big Cell Diagonal Map construction uses the mu Of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDiagonalMap.lean#L79-L82

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellDiagonalMap
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.BigCellDiagonalMap.muOf_mem (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : (muOf γ)ᴴ * Hb k * muOf γ = Hb k := by sorry
