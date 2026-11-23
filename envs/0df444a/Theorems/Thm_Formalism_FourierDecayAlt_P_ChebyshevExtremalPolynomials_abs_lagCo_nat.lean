-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_abs_lagCo_nat
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.abs_lagCo_nat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:19.200841+00:00
-- url     : https://prove2.me/theorems/3fdfc51e-9c88-4f9d-9285-b3886a189e01
-- title:
--   Chebyshev Extremal Polynomials: abs lag Co nat
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the abs lag Co nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L258-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L258-L274

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.abs_lagCo_nat (n : ℕ) (j : Fin (n + 1)) :
    |lagCo (fun i : Fin (n + 1) => ((i:ℕ):ℝ)) j| =
      ((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ)⁻¹ := by sorry
