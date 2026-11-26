-- Prove2me | Theorems.Thm_Aux_w_53_hermite_hasDerivAt_h1D
-- name    : Aux_w_53_hermite.hasDerivAt_h1D
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:40.724974+00:00
-- url     : https://prove2.me/theorems/48062c44-8960-571d-bf1b-7dd29a574987
-- title:
--   Derivative of a normalized probabilists' Hermite polynomial
-- statement:
--   Let $H_j$ be the probabilists' Hermite polynomial and set $h_j(x)=H_j(x)/\sqrt{j!}$. For every natural number $j$ and real $x$, $h_j$ is differentiable at $x$, with
--
--   $$
--   h'_j(x)=\begin{cases}0,&j=0,\\\sqrt j\,h_{j-1}(x),&j>0.\end{cases}
--   $$
--
--   This is the lowering identity for the normalized Hermite polynomials.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5HermiteFoundations.lean, Aux_w_53_hermite.hasDerivAt_h1D, lines 162–181.

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

theorem Aux_w_53_hermite.hasDerivAt_h1D (j : ℕ) (x : ℝ) : HasDerivAt (Aux_w_53_hermite.h1D j) (Aux_w_53_hermite.h1D_deriv j x) x := by sorry
