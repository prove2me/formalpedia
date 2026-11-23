-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_pair_small
-- name    : Formalism.FourierDecayAlt.P.Sz4.pair_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:04.902813+00:00
-- url     : https://prove2.me/theorems/676bf0e8-0898-463b-89d2-374d82d91d90
-- title:
--   Sz4: pair small
-- statement:
--   The Sz4 construction uses the pair small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L199-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L199-L207

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

theorem Formalism.FourierDecayAlt.P.Sz4.pair_small (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (i j : ℕ) (hij : i < j) :
    |(de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))| ≤ 1 / 4 := by sorry
