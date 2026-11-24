-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordNormLpLemmas_normW_Lp
-- name    : Formalism.FourierDecayAlt.P.WordNormLpLemmas.normW_Lp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:25.195867+00:00
-- url     : https://prove2.me/theorems/dd5b2869-7d73-4b20-88c5-a608fb0f4730
-- title:
--   Word Norm Lp Lemmas: norm W Lp
-- statement:
--   The Word Norm Lp Lemmas construction uses the norm W Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremCorollary.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremCorollary.lean#L13-L17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremCorollary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordNormLpLemmas
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix

theorem Formalism.FourierDecayAlt.P.WordNormLpLemmas.normW_Lp {S : Type} {K : ℕ} (nn : ℝ → ℝ) (sl : Fin K → S) (y : Fin K → ℝ) :
    normW nn (Lp sl y) = ∏ a, nn (y a) := by sorry
