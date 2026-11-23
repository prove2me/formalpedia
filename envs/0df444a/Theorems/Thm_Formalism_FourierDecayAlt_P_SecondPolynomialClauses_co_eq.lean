-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_co_eq
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.co_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:24.290804+00:00
-- url     : https://prove2.me/theorems/0c3e871f-d0aa-4d09-97a5-32f02efd285a
-- title:
--   Second Polynomial Clauses: co eq
-- statement:
--   The Second Polynomial Clauses construction uses the co eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L204-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L204-L211

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.co_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hg : ∀ a, Function.Injective (grid a))
    (j : Fin K → Fin (d + 1)) : |coProd grid j| = (∏ a, cg grid a) * Formalism.FourierDecayAlt.F7.thGrid grid j := by sorry
