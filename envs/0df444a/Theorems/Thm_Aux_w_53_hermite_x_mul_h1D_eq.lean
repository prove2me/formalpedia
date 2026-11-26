-- Prove2me | Theorems.Thm_Aux_w_53_hermite_x_mul_h1D_eq
-- name    : Aux_w_53_hermite.x_mul_h1D_eq
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:09.301869+00:00
-- url     : https://prove2.me/theorems/dc1d165e-13d4-4369-aff4-abcd38194d35
-- title:
--   Multiplication recurrence for normalized Hermite polynomials
-- statement:
--   For every natural j and real x, let h_j=He_j/√(j!) be the normalized probabilists' Hermite polynomial. Then $$xh_j(x)=\sqrt{j+1}\,h_{j+1}(x)+\begin{cases}0&j=0,\\\sqrt j\,h_{j-1}(x)&j>0.\end{cases}$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteFoundations.lean, lines 922–924.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
import Theorems.Thm_Aux_w_53_hermite_derivative_hermite
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

theorem Aux_w_53_hermite.x_mul_h1D_eq (j : ℕ) (x : ℝ) :
    x * Aux_w_53_hermite.h1D j x = Real.sqrt (j + 1 : ℝ) * Aux_w_53_hermite.h1D (j + 1) x +
      (if j = 0 then 0 else Real.sqrt (j : ℝ) * Aux_w_53_hermite.h1D (j - 1) x) := by sorry
