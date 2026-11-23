-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_site_step_of
-- name    : Formalism.FourierDecayAlt.P.Wd7.site_step_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:53.524657+00:00
-- url     : https://prove2.me/theorems/dc9d6fd9-6fad-4c99-83ac-ae99b961523a
-- title:
--   Wd7: site step of
-- statement:
--   The Wd7 construction uses the site step of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L643-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L643-L744

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd7.site_step_of
    (hE1 : ExchangePlusFactor) (hE2 : ExchangeMinusFactorStar) (hE3 : ExchangeMinusFactorTranspose) (hE4 : ExchangePlusFactorTranspose)
    (σ : Site A) (QQ QQ' : K → M2 A) (w : List (Letter K S))
    (hσ : IsSite σ) (hQ : QQCommutes QQ σ)
    (hrec : ∀ Y, star Y = Y → QQ' Y = (Ts σ Y)ᴴ * QQ Y * Ts σ Y) (hw : Good w) :
    star (bT σ w) * RRw QQ w * bT σ w = RRw QQ' w := by sorry
