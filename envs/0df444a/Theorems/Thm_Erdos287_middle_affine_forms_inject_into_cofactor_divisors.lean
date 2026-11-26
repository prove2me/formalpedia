-- Prove2me | Theorems.Thm_Erdos287_middle_affine_forms_inject_into_cofactor_divisors
-- name    : Erdos287.middle_affine_forms_inject_into_cofactor_divisors
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T19:13:47.397794+00:00
-- url     : https://prove2.me/theorems/ca6f5022-148e-5bee-9487-ee0b04179d8d
-- title:
--   Middle affine forms inject into divisors of the endpoint cofactors
-- statement:
--   Fix an oriented adjacent-multiple identity $wP_3-vP_1=1$ between two affine forms. Suppose each primitive middle form $P_2$ has identities $yP_2-uP_1=1$ and $zP_3-xP_2=1$, with $u,z$ at most $B$ and ratios $u/v,z/w<11/4$. The middle forms inject into the positive divisors $d$ of $vw$ satisfying $v+d\le B$, $vw\le(B-w)d$, and $4v/7<d<7v/4$.
-- source:
--   Erdős #287, finite compatibility constraints for the grouped adjacent-omission sieve.

import Mathlib

theorem Erdos287.middle_affine_forms_inject_into_cofactor_divisors (mid : Finset (ℕ × ℕ)) (a A c C v w cap : ℕ)
    (ha : 0 < a) (hv : 0 < v) (hw : 0 < w)
    (hl : v * a = w * c) (hc : w * C = v * A + 1)
    (hprimitive : ∀ p ∈ mid, p.1.Coprime p.2)
    (hedge : ∀ p ∈ mid, ∃ u y x z : ℕ,
      0 < x ∧ 0 < y ∧ u ≤ cap ∧ z ≤ cap ∧ 4 * u < 11 * v ∧ 4 * z < 11 * w ∧
      u * a = y * p.1 ∧ x * p.1 = z * c ∧ y * p.2 = u * A + 1 ∧ z * C = x * p.2 + 1) :
    mid.card ≤ ((v * w).divisors.filter (fun d =>
      v + d ≤ cap ∧ v * w ≤ (cap - w) * d ∧ 4 * d < 7 * v ∧ 4 * v < 7 * d)).card := by sorry
