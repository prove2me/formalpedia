-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_pt_inv_last
-- name    : Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.pt_inv_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:04.297282+00:00
-- url     : https://prove2.me/theorems/e2c01ba1-54aa-4280-b863-cdd08034165e
-- title:
--   Reversed Index Last Block: pt inv last
-- statement:
--   The Reversed Index Last Block construction uses the pt inv last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondKernelPropertyKernel.lean#L151-L158

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

theorem Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.pt_inv_last {K : Type} [CommRing K] (l : List ℕ) (t : ℕ → Kˣ) (N : Fin (l ++ [1]).sum)
    (hN : N.val + 1 = (l ++ [1]).sum) : (pt (l ++ [1]) t)⁻¹ N N = (((t l.length)⁻¹ : Kˣ) : K) := by sorry
