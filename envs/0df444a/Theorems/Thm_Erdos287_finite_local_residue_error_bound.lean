-- Prove2me | Theorems.Thm_Erdos287_finite_local_residue_error_bound
-- name    : Erdos287.finite_local_residue_error_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:51:18.010591+00:00
-- url     : https://prove2.me/theorems/f3f08c70-26e8-567a-926d-5a3f7980d05b
-- title:
--   Finite local residue averaging for prime distribution errors
-- statement:
--   Let $P$ be a finite set of coordinates, let $\mathcal Q$ be a finite family of subsets of $P$, and let each coordinate have a common finite nonempty set of $k$ choices. For each $q\in\mathcal Q$ and local choice $b$ on $q$, let $0\le E_q(b)\le G(q)$. Suppose that for every global choice $a$ on $P$, $\sum_{q\in\mathcal Q} E_q(a|_q)\le B$. Then
--
--   $$\sum_{q\in\mathcal Q}\sum_b E_q(b)\le \sqrt B\left(\sum_{q\in\mathcal Q} k^{2|q|}G(q)\right)^{1/2}.$$
--
--   For squarefree moduli, the coordinates represent primes and the local choices represent a bounded menu of invertible residues at each prime.
-- source:
--   Polymath8b, Variants of the Selberg sieve, and bounded intervals containing many primes, Section 4.2, https://arxiv.org/abs/1407.4897. Application to the Erdős 287 grouped prime-form sieve.

import Mathlib

theorem Erdos287.finite_local_residue_error_bound (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [Nonempty κ]
    (Q : Finset (Finset ι)) (E : (q : Finset ι) → (q → κ) → ℝ)
    (G : Finset ι → ℝ) (B : ℝ)
    (hE : ∀ q ∈ Q, ∀ b : q → κ, 0 ≤ E q b ∧ E q b ≤ G q)
    (hB : ∀ a : ι → κ, (∑ q ∈ Q, E q (fun i => a i)) ≤ B) :
    (∑ q ∈ Q, ∑ b : q → κ, E q b) ≤ Real.sqrt B *
      Real.sqrt (∑ q ∈ Q, ((Fintype.card κ : ℝ) ^ q.card) ^ 2 * G q) := by sorry
