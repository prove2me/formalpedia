-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_eval_b
-- name    : Formalism.FourierDecayAlt.P.Mx7.DD_eval_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:33.648804+00:00
-- url     : https://prove2.me/theorems/4fc2335e-7bbe-4212-b735-e8bae1abcd62
-- title:
--   Mx7: DD eval b
-- statement:
--   The Mx7 construction uses the DD eval b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L392-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L392-L406

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section

theorem Formalism.FourierDecayAlt.P.Mx7.DD_eval_b (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-(ρ l + 1)) =
    c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) := by sorry
