-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_revIn_revIn
-- name    : Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.revIn_revIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:53.796813+00:00
-- url     : https://prove2.me/theorems/67d21b35-b8ae-4bc8-bd4c-f3e356d41fa0
-- title:
--   Reversed Index Last Block: rev In rev In
-- statement:
--   The Reversed Index Last Block construction uses the rev In rev In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L112-L120

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

theorem Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  := by sorry
