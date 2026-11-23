-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_norm
-- name    : Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:55.669769+00:00
-- url     : https://prove2.me/theorems/04fed8a1-7878-4293-8bc1-3284b4217678
-- title:
--   Gram Conjugation Norm: gram norm
-- statement:
--   The Gram Conjugation Norm construction uses the gram norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L71-L76

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
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_norm (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : ‖gram k V P‖ = (gram k V P).re := by sorry
