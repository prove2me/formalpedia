-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordNormLpLemmas_cg_pos
-- name    : Formalism.FourierDecayAlt.P.WordNormLpLemmas.cg_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:26.233159+00:00
-- url     : https://prove2.me/theorems/74c1b698-b030-47e2-9564-996a5f149577
-- title:
--   Word Norm Lp Lemmas: cg pos
-- statement:
--   The Word Norm Lp Lemmas construction uses the cg pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremCorollary.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremCorollary.lean#L53-L57

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

theorem Formalism.FourierDecayAlt.P.WordNormLpLemmas.cg_pos {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) : 0 < cg y := by sorry
