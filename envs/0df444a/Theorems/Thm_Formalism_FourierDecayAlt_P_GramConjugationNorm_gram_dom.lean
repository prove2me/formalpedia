-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_dom
-- name    : Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:05.573797+00:00
-- url     : https://prove2.me/theorems/cf858774-47c0-4f2f-b59a-cd2d2428ce70
-- title:
--   Gram Conjugation Norm: gram dom
-- statement:
--   The Gram Conjugation Norm construction uses the gram dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L78-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L78-L96

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

theorem Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_dom {ι : Type} (R : Finset ι) (c : ℝ) (k : Pt E → Pt E → ℂ)
    (T : ι → Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P (fun h h' => (c : ℂ) * k h h' - ∑ t ∈ R, T t h h')) :
    ∑ t ∈ R, (gram (T t) V P).re ≤ c * (gram k V P).re := by sorry
