-- Prove2me | Theorems.Thm_Erdos287_reflected_omissions_and_boundary_residue
-- name    : Erdos287.reflected_omissions_and_boundary_residue
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T12:51:54.017734+00:00
-- url     : https://prove2.me/theorems/a4c027f0-d202-5aa0-9552-8a776b16c254
-- title:
--   Reflection identity for omitted denominators and boundary terms modulo an odd prime
-- statement:
--   Let $p$ be an odd prime dividing $m+M$. Let $U$ be the nonmultiples of $p$ in $[m,M]$, $H=U\setminus D$, and $R=D\setminus U$. In $\mathbb F_p$ the reciprocal sum over $H$ minus the reciprocal sum over $R$ equals the negative reciprocal sum over $D$. The same equation holds with $H$ replaced by the subset of holes whose reflected partner $m+M-n$ is not a hole.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reflected_omissions_and_boundary_residue (D : Finset ℕ) (m M p : ℕ) (hp : p.Prime) (hodd : 2 < p)
    (hcenter : p ∣ m + M) :
    let U := (Finset.Icc m M).filter (fun n => ¬ p ∣ n)
    let H := U \ D
    let R := D \ U
    (∑ n ∈ H, (n : ZMod p)⁻¹) - (∑ n ∈ R, (n : ZMod p)⁻¹) =
        -(∑ n ∈ D, (n : ZMod p)⁻¹) ∧
      (∑ n ∈ H.filter (fun n => m + M - n ∉ H), (n : ZMod p)⁻¹) -
        (∑ n ∈ R, (n : ZMod p)⁻¹) = -(∑ n ∈ D, (n : ZMod p)⁻¹) := by sorry
