-- Prove2me | Theorems.Thm_BooleanMultilinear_off_cube_evaluation_requires_all_queries
-- name    : BooleanMultilinear.off_cube_evaluation_requires_all_queries
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:34.535929+00:00
-- url     : https://prove2.me/theorems/314bf216-3a31-4a94-ae5a-9ea0b238a345
-- title:
--   Exact off-cube multilinear evaluation requires every Boolean query
-- statement:
--   Fix a point $z\in F^r$ over a field, with each coordinate outside $\{0,1\}$. For every fixed proper subset of the Boolean cube there are two Boolean functions that agree throughout that subset but whose multilinear extensions differ at $z$.
--
--   Consequently, knowing the truth table on any fixed proper subset cannot determine that evaluation for every Boolean function.
-- source:
--   Local derivation: PvsNPMLEQueryBarrier.lean, queried_subset_does_not_determine_extension, from the Boolean Lagrange basis formula. Original declaration starts at line 11. The query conclusion follows from J. Thaler, Proofs, Arguments, and Zero-Knowledge, Lemma 3.6, equations (3.1) and (3.2), https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf.

import Mathlib
open MvPolynomial
open scoped BigOperators

theorem BooleanMultilinear.off_cube_evaluation_requires_all_queries {F : Type*} [Field F] {r : ℕ} (z : Fin r → F)
    (away : ∀ i, z i ≠ 0 ∧ z i ≠ 1)
    (queries : Finset (Fin r → Bool)) (few : queries.card < 2^r) :
    let extension (f : (Fin r → Bool) → Bool) : MvPolynomial (Fin r) F :=
      ∑ a ∈ Finset.univ.filter (fun a => f a = true), ∏ i, (if a i then X i else 1 - X i)
    ∃ f g : (Fin r → Bool) → Bool,
      (∀ a ∈ queries, f a = g a) ∧ eval z (extension f) ≠ eval z (extension g) := by sorry
