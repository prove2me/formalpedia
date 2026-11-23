-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_lagCo_ne_zero
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.lagCo_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:24.236005+00:00
-- url     : https://prove2.me/theorems/ae73a735-bf32-4295-9dc8-ac521e534379
-- title:
--   Second Polynomial Clauses: lag Co ne zero
-- statement:
--   The Second Polynomial Clauses construction uses the lag Co ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L192-L196

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

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    Formalism.FourierDecayAlt.F7.lagCo y j ≠ 0 := by sorry
