-- Prove2me | Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D_mul_phi
-- name    : Aux_w_53_hermite.hasDerivAt_h1D_mul_phi
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:05.259998+00:00
-- url     : https://prove2.me/theorems/521eee22-bbad-4da5-b3f4-3df797fde526
-- title:
--   Derivative of a Gaussian-weighted normalized Hermite polynomial
-- statement:
--   For every natural j and real x, put φ(x)=(2π)^(−1/2)e^(−x²/2) and h_j=He_j/√(j!). Then the real derivative exists and equals $$\frac{d}{dx}(h_j(x)\phi(x))=-\sqrt{j+1}\,h_{j+1}(x)\phi(x).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteFoundations.lean, lines 183–184.

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
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D
import Theorems.Thm_Aux_w_53_hermite_hasDerivAt_phi
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

theorem Aux_w_53_hermite.hasDerivAt_h1D_mul_phi (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => Aux_w_53_hermite.h1D j y * Aux_w_53_hermite.phi y) (-Real.sqrt (j + 1 : ℝ) * Aux_w_53_hermite.h1D (j + 1) x * Aux_w_53_hermite.phi x) x := by sorry
