-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LastBlockReversalIndices_entry
-- name    : Formalism.FourierDecayAlt.P.LastBlockReversalIndices.entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:18.195959+00:00
-- url     : https://prove2.me/theorems/cb716442-63e9-4bc4-8dc9-b3a84813dd2c
-- title:
--   Last Block Reversal Indices: entry
-- statement:
--   The Last Block Reversal Indices construction uses the entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L26-L44

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LastBlockReversalIndices
open Formalism.DoubleCosetMeasures MeasureTheory

theorem Formalism.FourierDecayAlt.P.LastBlockReversalIndices.entry {K : Type} [CommRing K] {n : ℕ} (N : Fin n) (hN : N.val + 1 = n)
    (V W U : Matrix (Fin n) (Fin n) K) (hV : IsLowUni V) (hU : IsUpUni U) :
    (V * W * U)⁻¹ N N = W⁻¹ N N := by sorry
