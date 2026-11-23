-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_eval_a
-- name    : Formalism.FourierDecayAlt.P.Mx7.DD_eval_a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:32.957492+00:00
-- url     : https://prove2.me/theorems/5d2466d6-20ed-47a9-8e84-6bf6f962b701
-- title:
--   Mx7: DD eval a
-- statement:
--   The Mx7 construction uses the DD eval a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L377-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean#L377-L390

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

theorem Formalism.FourierDecayAlt.P.Mx7.DD_eval_a (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-ρ l) =
    c * q1.eval (-ρ l) + M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by sorry
