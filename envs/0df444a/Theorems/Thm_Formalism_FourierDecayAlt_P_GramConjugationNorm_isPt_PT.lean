-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_isPt_PT
-- name    : Formalism.FourierDecayAlt.P.GramConjugationNorm.isPt_PT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:12.855731+00:00
-- url     : https://prove2.me/theorems/7e8c1971-8736-4f12-bb0a-06bf03bdd51b
-- title:
--   Gram Conjugation Norm: is Pt PT
-- statement:
--   The Gram Conjugation Norm construction uses the is Pt PT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L9-L31

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

theorem Formalism.FourierDecayAlt.P.GramConjugationNorm.isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by sorry
