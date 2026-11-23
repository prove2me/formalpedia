-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_frameM_row
-- name    : Formalism.DworkPowerSeriesWeights.sum_frameM_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:48.004803+00:00
-- url     : https://prove2.me/theorems/3baa7ca6-caa3-452a-a46e-71fb4e56e9a8
-- title:
--   Dwork Power Series Weights: sum frame M row
-- statement:
--   The Dwork Power Series Weights construction uses the sum frame M row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L144-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean#L144-L161

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]

theorem Formalism.DworkPowerSeriesWeights.sum_frameM_row (x : ZMod d × Fin N0 × Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    (∑ j : ZV d N0 N1, MvPolynomial.C (frameM (N1 := N1) x j (s, i, b)) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) =
      ∑ a : Fin N0, MvPolynomial.C (x (s, i, a)) * MvPolynomial.X (s, a, b) := by sorry
