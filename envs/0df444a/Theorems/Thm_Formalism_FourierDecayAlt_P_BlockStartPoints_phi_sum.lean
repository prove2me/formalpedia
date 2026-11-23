-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_phi_sum
-- name    : Formalism.FourierDecayAlt.P.BlockStartPoints.phi_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:18.719801+00:00
-- url     : https://prove2.me/theorems/7d7c6c02-4409-4932-8e4f-121ff731170f
-- title:
--   Block Start Points: phi sum
-- statement:
--   The Block Start Points construction uses the phi sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockStartPoints.lean#L131-L138

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

theorem Formalism.FourierDecayAlt.P.BlockStartPoints.phi_sum {τ J : Type} (S : Finset τ) (Js : Finset J) (m : τ → τ → ℝ) (g : J → τ → τ → ℝ) :
    ∑ t ∈ S, ∑ t' ∈ S, m t t' * ∑ j ∈ Js, g j t t' =
      ∑ j ∈ Js, ∑ t ∈ S, ∑ t' ∈ S, m t t' * g j t t' := by sorry
