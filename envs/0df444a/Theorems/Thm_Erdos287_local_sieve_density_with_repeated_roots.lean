-- Prove2me | Theorems.Thm_Erdos287_local_sieve_density_with_repeated_roots
-- name    : Erdos287.local_sieve_density_with_repeated_roots
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T20:04:05.732366+00:00
-- url     : https://prove2.me/theorems/82d3b670-2638-442c-b928-b70cb9237a77
-- title:
--   Local affine sieve density with repeated zero residues
-- statement:
--   Let $R$ be a finite set of allowed residues and $H$ the distinct roots of a finite family of auxiliary coordinates, with $H\subsetneq R$. A residue has weight equal to the product of auxiliary weights at its root, with empty product one. If each auxiliary weight has modulus at most $\varepsilon\le1$, the total weight differs from $|R\setminus H|$ by at most $|H|\varepsilon$. Sifting an additional root $j$ multiplies the unweighted surviving count by $1-1/|R\setminus H|$ if $j$ is a new allowed root, and by one otherwise. The normalized weighted error for a new root is at most $|H|\varepsilon/|R\setminus H|$.
-- source:
--   Weighted affine sieve for Erdős Problem 287.

import Mathlib

theorem Erdos287.local_sieve_density_with_repeated_roots {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (T : Finset ι) (R : Finset ρ) (root : ι → ρ) (j : ρ)
    (w : ι → ℂ) (ε : ℝ) (hε : ε ≤ 1)
    (hw : ∀ i ∈ T, ‖w i‖ ≤ ε)
    (hroot : T.image root ⊆ R) (hproper : (T.image root).card < R.card) :
    let H := T.image root
    let Q := R \ H
    let K := ∑ x ∈ R, ∏ i ∈ T.filter (fun i => root i = x), w i
    let g : ℝ := if j ∈ Q then 1 / (Q.card : ℝ) else 0
    ‖K - (Q.card : ℂ)‖ ≤ (H.card : ℝ) * ε ∧
      (Q.card : ℝ) * (1 - g) = ((Q.erase j).card : ℝ) ∧
      (j ∈ Q → ‖1 - K / (Q.card : ℂ)‖ ≤ (H.card : ℝ) * ε / Q.card) := by sorry
