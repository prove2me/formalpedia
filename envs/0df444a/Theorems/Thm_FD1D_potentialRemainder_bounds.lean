-- Prove2me | Theorems.Thm_FD1D_potentialRemainder_bounds
-- name    : FD1D.potentialRemainder_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:28.682675+00:00
-- url     : https://prove2.me/theorems/01b5dc5f-d5a6-475d-962b-b2f4c3ab8768
-- title:
--   FD1 D: potential Remainder bounds
-- statement:
--   Equation (10): `0 ≤ R ≤ sum H_ell ≤ L H_L`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L184-L200
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L184-L200

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.potentialRemainder_bounds
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q h : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hq0 : ∀ d v, 0 ≤ q d v)
    (hq1 : ∀ d v, q d v ≤ 1)
    (hmajor : ∀ d v,
      nodeMass d v ≤ ((N d v : ℝ) + a) * h d v)
    (hmono : Monotone (hazardEnergy h)) :
    0 ≤ potentialRemainder L a N q ∧
      potentialRemainder L a N q ≤
        ∑ d ∈ Finset.range L, hazardEnergy h (d + 1) ∧
      (∑ d ∈ Finset.range L, hazardEnergy h (d + 1)) ≤
        (L : ℝ) * hazardEnergy h L := by sorry
