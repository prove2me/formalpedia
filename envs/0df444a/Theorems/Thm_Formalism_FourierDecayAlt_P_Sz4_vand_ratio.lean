-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_ratio
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:18.14934+00:00
-- url     : https://prove2.me/theorems/7d2e4228-c843-4083-a599-bcf506d2d421
-- title:
--   Sz4: vand ratio
-- statement:
--   The Sz4 construction uses the vand ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L269-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L269-L277

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.vand_ratio (p : ℕ) (x y : ℕ → ℝ) (r : ℕ → ℕ → ℝ)
    (h : ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ p → x i - x j = r i j * (y i - y j)) :
    Vand p x = (∏ i ∈ Icc 1 p, ∏ j ∈ Ioc i p, r i j) * Vand p y := by sorry
