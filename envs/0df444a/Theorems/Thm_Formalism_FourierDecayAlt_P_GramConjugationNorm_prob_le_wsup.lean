-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_prob_le_wsup
-- name    : Formalism.FourierDecayAlt.P.GramConjugationNorm.prob_le_wsup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:00.821135+00:00
-- url     : https://prove2.me/theorems/eb18813a-88a1-4c6d-9a91-1e73c1552693
-- title:
--   Gram Conjugation Norm: prob le wsup
-- statement:
--   The Gram Conjugation Norm construction uses the prob le wsup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L103-L113

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramConjugationNorm
open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate
variable {W : Type} [Fintype W]

theorem Formalism.FourierDecayAlt.P.GramConjugationNorm.prob_le_wsup (len : W → ℕ) (B : ℕ) (th : W → ℝ) (hth : IsProb len B th) (g : W → ℝ) :
    ∑ w, th w * g w ≤ wsup len B g := by sorry
