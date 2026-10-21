-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_chain_strict
-- name    : DerivativeChainPrivate.normalized_fifth_chain_strict
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T23:14:29.232376+00:00
-- url     : https://prove2.me/theorems/6501216c-41d6-4ce4-9e4f-64a28d39ca85
-- title:
--   Complete compatible fifteen-row chain in the strict normalized fifth-power case
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, and set $q_\beta(z)=z^3-7z-91\beta$. There is a chain $z_1,\ldots,z_{15}$ with
--   $$D^{15-m}(q_\beta^5)(z_m)=0\quad(1\le m\le15),\qquad z_1=0,$$
--   whose real and imaginary coordinate sequences are both nondecreasing. The final five entries coincide at a root of the source cubic:
--   $$z_{11}=\cdots=z_{15},\qquad q_\beta(z_{15})=0.$$
--   The chain satisfies
--   $$\sum_{m=1}^{14}|z_{m+1}-z_m|\le\sqrt2\,|z_{15}|.$$
--   This is the complete normalized selector. Separate boundary, affine-normalization and zero-second-moment results extend it to the unrestricted parameter cases of the cubic fifth-power radius theorem.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; H5_COMPLETE_CHAIN.md, complete compatible chain, with the fixed normalization stated explicitly.

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_decic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_nonic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_octic_step_with_bounds
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_selected_sextic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_septic_step_with_bounds
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_source_step
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_chain_strict (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im) :
    ∃ z : Fin 15 → ℂ,
      (∀ i, (derivative^[15-(i.val+1)] ((X^3-C 7*X-91*C β)^5)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin 15, 10 ≤ i.val → z i=z 14) ∧
      (z 14)^3-7*z 14-91*β=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z 14‖ := by sorry
