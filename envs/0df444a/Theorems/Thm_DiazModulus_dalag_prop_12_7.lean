-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_7
-- name    : DiazModulus.dalag_prop_12_7
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-15T05:43:46.85732+00:00
-- url     : https://prove2.me/theorems/232c6298-bc4f-4efd-8e7b-670c9819d124
-- title:
--   DALAG Prop. 12.7: if E ⊂ K has Property (A B; C 0) and V ⊂ Kᵈ is a K-subspace of dimension n with V ∩ kᵈ = {0}, then dim_k(V ∩ Eᵈ) ≤ n(n + 1)/2
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A $k$-vector subspace $E$ of $K$ has *Property (A B; C 0)* (DALAG §12.1.3) if every non-zero matrix $M$ with entries in $E$ is $k$-equivalent to a block matrix $\begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ a regular square matrix: there are invertible matrices $P$, $Q$ with entries in $k$ and $r \ge 1$ such that every entry of $PMQ$ whose row and column indices are both at least $r$ vanishes, and the upper left $r \times r$ block of $PMQ$ is invertible. A vector of $K^d$ is *$k$-rational* if its coordinates lie in $k$.
--
--   Let $E \subseteq K$ be a $k$-vector subspace with Property (A B; C 0), and let $V \subseteq K^d$ be a $K$-vector subspace of dimension $n$ that contains no non-zero $k$-rational vector. Then $V \cap E^d$ is a finite-dimensional $k$-vector space, and
--   $$\dim_k\big(V \cap E^d\big) \le \frac{n(n + 1)}{2}.$$
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.7 (p. 426), with the Property of §12.1.3 (p. 424). Proved by strong induction on d from its inductive step, DiazModulus.dalag_prop_12_7_step. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_7 {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hE : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    {d : ℕ} (V : Submodule K (Fin d → K))
    (hV : ∀ v ∈ V, (∀ i, ∃ c : k, v i = algebraMap k K c) → v = 0) :
    FiniteDimensional k ↥(V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E)) ∧
    Module.finrank k ↥(V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E)) ≤
      Module.finrank K ↥V * (Module.finrank K ↥V + 1) / 2 := by
  sorry

end DiazModulus
