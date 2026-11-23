-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SchurNormSquareBounds_row_le
-- name    : Formalism.FourierDecayAlt.P.SchurNormSquareBounds.row_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:22.1048+00:00
-- url     : https://prove2.me/theorems/2486fad2-b881-499f-832c-64c87ac50ae4
-- title:
--   Schur Norm Square Bounds: row le
-- statement:
--   The Schur Norm Square Bounds construction uses the row le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RowNormSquareBounds.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RowNormSquareBounds.lean#L22-L44

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RowNormSquareBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SchurNormSquareBounds
open Finset

theorem Formalism.FourierDecayAlt.P.SchurNormSquareBounds.row_le {G ι : Type} [AddCommGroup G] [DecidableEq ι] (La : AddSubgroup G) (T : Finset ι)
    (τ : ι → G) (ψ : G → ℝ) (ε : ℝ) (hinj : Set.InjOn τ T)
    (hco : ∀ t ∈ T, ∀ t' ∈ T, τ t - τ t' ∈ La)
    (hS : ∀ S : Finset G, (∀ l ∈ S, l ∈ La ∧ l ≠ 0) → ∑ l ∈ S, ψ l ≤ ε) (t : ι) (ht : t ∈ T) :
    ∑ t' ∈ T.erase t, ψ (τ t - τ t') ≤ ε ∧ ∑ t' ∈ T.erase t, ψ (τ t' - τ t) ≤ ε := by sorry
