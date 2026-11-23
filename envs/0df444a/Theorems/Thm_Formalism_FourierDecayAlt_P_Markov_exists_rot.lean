-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_exists_rot
-- name    : Formalism.FourierDecayAlt.P.Markov.exists_rot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:24.40605+00:00
-- url     : https://prove2.me/theorems/3c8e3dae-0f2e-4542-a98b-aff0dd23d659
-- title:
--   Markov: exists rot
-- statement:
--   The Markov construction uses the exists rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L183-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L183-L203

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

theorem Formalism.FourierDecayAlt.P.Markov.exists_rot (a b : ℝ) (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) :
    ∃ A B : ℝ[X], B.degree < n ∧ ∀ y z : ℝ, y ^ 2 + z ^ 2 = 1 →
      p.eval (a * y + b * z) = A.eval y + z * B.eval y := by sorry
