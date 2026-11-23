-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_ratio_ge
-- name    : Formalism.FourierDecayAlt.P.Sz4.prod_ratio_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:08.047895+00:00
-- url     : https://prove2.me/theorems/3d0cac56-2e34-4807-a0a9-aeb13ea41df8
-- title:
--   Sz4: prod ratio ge
-- statement:
--   The Sz4 construction uses the prod ratio ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L449-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L449-L456

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

theorem Formalism.FourierDecayAlt.P.Sz4.prod_ratio_ge (s : Finset ℕ) (f g : ℕ → ℝ) (B : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (hf : ∀ i ∈ s, 0 < f i) (h : ∏ i ∈ s, g i / f i ≤ Real.exp B) :
    Real.exp (-B) ≤ ∏ i ∈ s, f i / g i := by sorry
