-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_schur_abs
-- name    : Formalism.FourierDecayAlt.P.TA2.schur_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:04.244648+00:00
-- url     : https://prove2.me/theorems/b75101e4-f26b-4943-9958-3cf22c96e480
-- title:
--   TA2: schur abs
-- statement:
--   The TA2 construction uses the schur abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L85-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L85-L106

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2

theorem Formalism.FourierDecayAlt.P.TA2.schur_abs {α : Type} (T : Finset α) (c : α → α → ℝ) (A B : α → ℝ) (ep : ℝ)
    (hA : ∀ t ∈ T, 0 ≤ A t) (hB : ∀ t ∈ T, 0 ≤ B t)
    (row : ∀ t ∈ T, ∑ t' ∈ T, c t t' ≤ ep) (col : ∀ t' ∈ T, ∑ t ∈ T, c t t' ≤ ep) :
    ∑ t ∈ T, ∑ t' ∈ T, c t t' * ((A t + B t') / 2)
      ≤ ep * ((∑ t ∈ T, A t + ∑ t ∈ T, B t) / 2) := by sorry
