-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_perturbation_disk
-- name    : DerivativeChainPrivate.cubic_perturbation_disk
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:04:43.003401+00:00
-- url     : https://prove2.me/theorems/f0e01345-4c29-4c40-8eef-9faa017d641f
-- title:
--   A centered perturbation has a controlled containing disk
-- statement:
--   Let $u,v,w,o,a\in\mathbb C$, $t\ge0$, and suppose $|u-o|,|v-o|,|w-o|\le R$. Then each of $u+ta$, $v-ta/2$, $w-ta/2$ has distance at most $R+t|a|$ from $o$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L2048-L2066

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.cubic_perturbation_disk (u v w o a : ℂ) (R t : ℝ) (ht : 0 ≤ t)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R) :
    ‖u+(t : ℂ)*a-o‖ ≤ R+t*‖a‖ ∧
      ‖v-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ ∧ ‖w-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ := by sorry
