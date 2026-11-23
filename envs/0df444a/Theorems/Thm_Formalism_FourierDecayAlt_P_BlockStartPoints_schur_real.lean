-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_schur_real
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.schur_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:19.924811+00:00
-- url     : https://prove2.me/theorems/cec70197-52fc-4e28-a091-819f0f3b09e5
-- title:
--   Block Start Points: schur real
-- statement:
--   The Block Start Points construction uses the schur real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L104-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L104-L129

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.schur_real {τ : Type} (S : Finset τ) (m : τ → τ → ℝ) (ep M : ℝ) (hep : 0 ≤ ep)
    (row : ∀ t ∈ S, ∑ t' ∈ S, m t t' ≤ ep) (col : ∀ t' ∈ S, ∑ t ∈ S, m t t' ≤ ep)
    (a b : τ → ℝ) (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t)
    (hA : ∑ t ∈ S, a t ≤ M) (hB : ∑ t ∈ S, b t ≤ M) :
    ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a t + b t') / 2) ≤ ep * M := by sorry
