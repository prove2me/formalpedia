-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_ratio_le
-- name    : Formalism.FourierDecayAlt.P.Sz4.prod_ratio_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:57.021145+00:00
-- url     : https://prove2.me/theorems/4aba142b-8278-40c4-a54a-8ca6e568ba51
-- title:
--   Sz4: prod ratio le
-- statement:
--   The Sz4 construction uses the prod ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L439-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L439-L447

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

theorem Formalism.FourierDecayAlt.P.Sz4.prod_ratio_le (s : Finset ℕ) (f g : ℕ → ℝ) (ε : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ (1 + ε) * g i) :
    ∏ i ∈ s, f i / g i ≤ Real.exp ((s.card : ℝ) * ε) := by sorry
