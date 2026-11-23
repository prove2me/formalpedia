-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_coeff_id
-- name    : Formalism.FourierDecayAlt.P.LEx2.coeff_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:20:08.656801+00:00
-- url     : https://prove2.me/theorems/4e851b79-daf3-443d-a458-e1b04ec5c836
-- title:
--   LEx2: coeff id
-- statement:
--   The LEx2 construction uses the coeff id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L117-L125

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx2.coeff_id (s : Finset ℝ) (d k j : ℕ) (hs : s.card = d + 1) (hk : k ≤ d) :
    ∑ x ∈ s, (Lagrange.basis s id x).coeff j * x ^ k = if j = k then 1 else 0 := by sorry
