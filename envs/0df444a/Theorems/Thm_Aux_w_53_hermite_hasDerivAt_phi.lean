-- Prove2me | Theorems.Thm_Aux_w_53_hermite_hasDerivAt_phi
-- name    : Aux_w_53_hermite.hasDerivAt_phi
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:30.043608+00:00
-- url     : https://prove2.me/theorems/148aca51-5a98-4cb3-b28a-6e103531812f
-- title:
--   Derivative of the standard Gaussian density
-- statement:
--   Let $\phi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ be the standard real Gaussian density. At every $x\in\mathbb R$ it has derivative
--
--   $$
--   \phi'(x)=-x\phi(x).
--   $$
--
--   This supplies the differential identity used in Gaussian-weighted Hermite calculations.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5HermiteFoundations.lean, Aux_w_53_hermite.hasDerivAt_phi, lines 42–53.

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
set_option autoImplicit false
namespace Aux_w_53_hermite
end Aux_w_53_hermite
open Aux_w_53_hermite
open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

theorem Aux_w_53_hermite.hasDerivAt_phi (x : ℝ) : HasDerivAt Aux_w_53_hermite.phi (-x * Aux_w_53_hermite.phi x) x := by sorry
