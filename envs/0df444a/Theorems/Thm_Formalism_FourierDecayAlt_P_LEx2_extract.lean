-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_extract
-- name    : Formalism.FourierDecayAlt.P.LEx2.extract
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:40.771017+00:00
-- url     : https://prove2.me/theorems/62554a6f-abaa-47ea-880b-06859b987464
-- title:
--   LEx2: extract
-- statement:
--   The LEx2 construction uses the extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L127-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L127-L155

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

theorem Formalism.FourierDecayAlt.P.LEx2.extract (N d : ℕ) (grid : Fin N → Finset ℝ) (hg : ∀ a, (grid a).card = d + 1)
    (c : (Fin N → Fin (d + 1)) → ℂ) (κ : Fin N → Fin (d + 1)) :
    c κ = ∑ g ∈ Fintype.piFinset grid, ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) *
      ∑ κ' : Fin N → Fin (d + 1), ((∏ a, (g a) ^ (κ' a : ℕ) : ℝ) : ℂ) * c κ' := by sorry
