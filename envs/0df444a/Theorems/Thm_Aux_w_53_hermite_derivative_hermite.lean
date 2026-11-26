-- Prove2me | Theorems.Thm_Aux_w_53_hermite_derivative_hermite
-- name    : Aux_w_53_hermite.derivative_hermite
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:18.058849+00:00
-- url     : https://prove2.me/theorems/f4654216-f1bf-5cfe-802f-9135d0985e0a
-- title:
--   Derivative recurrence for probabilists' Hermite polynomials
-- statement:
--   For every natural j, let He_j be the integer-coefficient probabilists' Hermite polynomial. Its polynomial derivative satisfies $$\frac{d}{dx}\operatorname{He}_{j+1}(x)=(j+1)\operatorname{He}_j(x).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteFoundations.lean, lines 58–59.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

theorem Aux_w_53_hermite.derivative_hermite (j : ℕ) :
    Polynomial.derivative (Polynomial.hermite (j + 1)) = C ((j + 1 : ℕ) : ℤ) * Polynomial.hermite j := by sorry
