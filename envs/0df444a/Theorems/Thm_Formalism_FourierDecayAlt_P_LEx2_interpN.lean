-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_interpN
-- name    : Formalism.FourierDecayAlt.P.LEx2.interpN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:08.04858+00:00
-- url     : https://prove2.me/theorems/f1b2be21-5734-4bc9-a235-27e91b042152
-- title:
--   LEx2: interp N
-- statement:
--   The LEx2 construction uses the interp N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L20-L39

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
open MvPolynomial

theorem Formalism.FourierDecayAlt.P.LEx2.interpN (N n : ℕ) (grid : Fin N → Finset ℝ) (hg : ∀ a, (grid a).card = n + 1)
    (Q : MvPolynomial (Fin N) ℝ) (hQ : ∀ a, Q.degreeOf a ≤ n) (Y : Fin N → ℝ) :
    eval Y Q = ∑ g ∈ Fintype.piFinset grid,
      (∏ a, (Lagrange.basis (grid a) id (g a)).eval (Y a)) * eval g Q := by sorry
