-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordNormLpLemmas_key
-- name    : Formalism.FourierDecayAlt.P.WordNormLpLemmas.key
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:07.709595+00:00
-- url     : https://prove2.me/theorems/3bc37252-79fb-4063-8c06-4c6de5353bf1
-- title:
--   Word Norm Lp Lemmas: key
-- statement:
--   The Word Norm Lp Lemmas construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremCorollary.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremCorollary.lean#L25-L45

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

theorem Formalism.FourierDecayAlt.P.WordNormLpLemmas.key (a b Q W N N' T c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 < Q) (hW : 0 < W)
    (hN : 0 < N) (hN' : 0 < N') (hT : 0 ≤ T) (hc : 0 ≤ c) (hNT : N * N' / Q ≤ T ^ 2) :
    c * Real.sqrt (a * b / Q) / W ≤ c * T * ((a / (N * W) + b / (N' * W)) / 2) := by sorry
