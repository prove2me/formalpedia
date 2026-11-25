-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_splits_mem
-- name    : Formalism.FourierDecayAlt.P.JFxI.splits_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:52.356816+00:00
-- url     : https://prove2.me/theorems/b1add211-5427-4ec6-ae83-f8017a084d7d
-- title:
--   JFx I: splits mem
-- statement:
--   The JFx I construction uses the splits mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L138-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L138-L155

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.JFxI.splits_mem {α : Type*} : ∀ (w : List α), ∀ uv ∈ splits w,
    (∀ X ∈ uv.1, X ∈ w) ∧ (∀ X ∈ uv.2, X ∈ w) ∧ uv.2.length ≤ w.length
  := by sorry
