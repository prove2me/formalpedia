-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_lagCo_affine
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.lagCo_affine
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:47.511713+00:00
-- url     : https://prove2.me/theorems/83d93ae8-ae54-4c0a-b5fd-2d09d6ed16e1
-- title:
--   Chebyshev Extremal Polynomials: lag Co affine
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the lag Co affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L13-L20

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

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.lagCo_affine {d : ℕ} (c h : ℝ) (x : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    lagCo (fun i => c + h * x i) j = (h⁻¹) ^ d * lagCo x j := by sorry
