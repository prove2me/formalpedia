-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_betaL_ne_zero
-- name    : Formalism.FourierDecayAlt.P.GermRealisation.betaL_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:04.850378+00:00
-- url     : https://prove2.me/theorems/36814eeb-3c58-51f7-b256-8b9174630197
-- title:
--   Germ Realisation: beta L ne zero
-- statement:
--   The Germ Realisation construction uses the beta L ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsiNegBetaL.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsiNegBetaL.lean#L30-L34

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfFibres
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.GermRealisation.betaL_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by sorry
