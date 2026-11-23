-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_abs_U_mul_sin
-- name    : Formalism.FourierDecayAlt.P.Markov.abs_U_mul_sin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:17.50298+00:00
-- url     : https://prove2.me/theorems/8f2e053f-db0c-4242-a4bb-ae31b981b200
-- title:
--   Markov: abs U mul sin
-- statement:
--   The Markov construction uses the abs U mul sin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L87-L94

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset

theorem Formalism.FourierDecayAlt.P.Markov.abs_U_mul_sin (n k : ℕ) (hn : n ≠ 0) :
    |(Chebyshev.U ℝ ((n : ℤ) - 1)).eval (cos (th n k))| * |sin (th n k)| = 1 := by sorry
