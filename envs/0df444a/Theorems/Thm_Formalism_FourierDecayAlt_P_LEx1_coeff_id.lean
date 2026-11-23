-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_coeff_id
-- name    : Formalism.FourierDecayAlt.P.LEx1.coeff_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:26.805655+00:00
-- url     : https://prove2.me/theorems/6d3a58ca-b32c-4d41-b33e-e84f72965abb
-- title:
--   LEx1: coeff id
-- statement:
--   The LEx1 construction uses the coeff id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L74-L82

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx1.coeff_id (s : Finset ℝ) (d k j : ℕ) (hs : s.card = d + 1) (hk : k ≤ d) :
    ∑ x ∈ s, (Lagrange.basis s id x).coeff j * x ^ k = if j = k then 1 else 0 := by sorry
