-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_avg_le
-- name    : Formalism.FourierDecayAlt.P.GramConjugationNorm.avg_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:09.248646+00:00
-- url     : https://prove2.me/theorems/3c9abc26-6e8f-4343-be23-495bec44eb58
-- title:
--   Gram Conjugation Norm: avg le
-- statement:
--   The Gram Conjugation Norm construction uses the avg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramConjugationNorm.lean#L115-L127

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

theorem Formalism.FourierDecayAlt.P.GramConjugationNorm.avg_le {ι : Type} (R : Finset ι) (len : W → ℕ) (B : ℕ) (th : W → ℝ)
    (hth : IsProb len B th) (g : ι → W → ℝ) (S : W → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ w', ∑ t0 ∈ R, g t0 w' ≤ c * S w') :
    ∑ t0 ∈ R, ∑ w', th w' * g t0 w' ≤ c * wsup len B S := by sorry
