-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_hasDerivAt_list_sum
-- name    : Formalism.FourierDecayAlt.P.JFxI.hasDerivAt_list_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:11.323085+00:00
-- url     : https://prove2.me/theorems/5f95627a-facd-520e-a2d2-270d2ff301e0
-- title:
--   JFx I: has Deriv At list sum
-- statement:
--   The JFx I construction uses the has Deriv At list sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L123-L130

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxI.hasDerivAt_list_sum {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : List ι) (g : ι → ℝ → F)
    (g' : ι → F) {t : ℝ} (h : ∀ i ∈ L, HasDerivAt (g i) (g' i) t) :
    HasDerivAt (fun s => (L.map fun i => g i s).sum) (L.map g').sum t := by sorry
