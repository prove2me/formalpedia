-- Prove2me | Theorems.Thm_Aux_w_53_hermite_h1D_orthonormal_aux
-- name    : Aux_w_53_hermite.h1D_orthonormal_aux
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:53.883889+00:00
-- url     : https://prove2.me/theorems/97759674-2e9f-5ae9-ae0b-efc64b045dd1
-- title:
--   Gaussian orthonormality of normalized Hermite polynomials
-- statement:
--   Let j,k be natural numbers, let φ(x)=(2π)^(−1/2)e^(−x²/2), and let h_j(x)=He_j(x)/√(j!). The Lebesgue integral satisfies $$\int_{\mathbb R}h_j(x)h_k(x)\phi(x)\,dx=\begin{cases}1&j=k,\\0&j\ne k.\end{cases}$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteFoundations.lean, lines 408–409.

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
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D_mul_phi
import Theorems.Thm_Aux_w_53_hermite_tendsto_pow_mul_phi_atTop
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

theorem Aux_w_53_hermite.h1D_orthonormal_aux (j k : ℕ) :
    ∫ x : ℝ, Aux_w_53_hermite.h1D j x * Aux_w_53_hermite.h1D k x * Aux_w_53_hermite.phi x = if j = k then 1 else 0 := by sorry
