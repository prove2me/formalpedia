-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_pt_mul
-- name    : Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.pt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:43.075557+00:00
-- url     : https://prove2.me/theorems/3b36d299-17e9-4848-a8b5-bf9e4db7342d
-- title:
--   Reversed Index Last Block: pt mul
-- statement:
--   The Reversed Index Last Block construction uses the pt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L132-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L132-L149

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
open Formalism.DoubleCosetMeasures

theorem Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.pt_mul {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t * pt s (fun b => (t b)⁻¹) = (1 : Matrix (Fin s.sum) (Fin s.sum) K) := by sorry
