-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_7_step
-- name    : DiazModulus.dalag_prop_12_7_step
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-15T05:43:54.489637+00:00
-- url     : https://prove2.me/theorems/a5536416-6ecb-4310-b172-c3dc1f1316a1
-- title:
--   DALAG Prop. 12.7, inductive step: k-free v₁, …, v_ℓ in V ∩ Eᵈ give r ≤ dim V, r < d and ℓ − r k-free vectors in V₁ ∩ Eʳ, V₁ ⊂ Kʳ a K-subspace with V₁ ∩ kʳ = {0}
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A $k$-vector subspace $E$ of $K$ has *Property (A B; C 0)* (DALAG §12.1.3) if every non-zero matrix $M$ with entries in $E$ is $k$-equivalent to a block matrix $\begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ a regular square matrix: there are invertible matrices $P$, $Q$ with entries in $k$ and $r \ge 1$ such that every entry of $PMQ$ whose row and column indices are both at least $r$ vanishes, and the upper left $r \times r$ block of $PMQ$ is invertible. A vector of $K^d$ is *$k$-rational* if its coordinates lie in $k$.
--
--   Let $E \subseteq K$ be a $k$-vector subspace with Property (A B; C 0), let $V \subseteq K^d$ be a $K$-vector subspace that contains no non-zero $k$-rational vector, and let $v_1, \dots, v_\ell \in V \cap E^d$, with $\ell \ge 1$, be linearly independent over $k$. Then there are natural numbers $r$ and $\ell_1$ with $r + \ell_1 = \ell$, $r \le \dim_K V$ and $r < d$, a $K$-vector subspace $V_1 \subseteq K^r$ that contains no non-zero $k$-rational vector, and $w_1, \dots, w_{\ell_1} \in V_1 \cap E^r$ linearly independent over $k$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.7 (p. 426): the inductive step, with V₁ a K-vector subspace built from P·V, where P is the left factor of the k-equivalence; the printed text says "k-vector subspace" in the two places where a K-vector subspace is needed. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_7_step {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hE : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    {d ℓ : ℕ} (V : Submodule K (Fin d → K))
    (hV : ∀ v ∈ V, (∀ i, ∃ c : k, v i = algebraMap k K c) → v = 0)
    (v : Fin ℓ → Fin d → K) (hv : LinearIndependent k v) (hvV : ∀ j, v j ∈ V)
    (hvE : ∀ j i, v j i ∈ E) (hℓ : 0 < ℓ) :
    ∃ (r ℓ₁ : ℕ) (V₁ : Submodule K (Fin r → K)) (w : Fin ℓ₁ → Fin r → K),
      r + ℓ₁ = ℓ ∧ r ≤ Module.finrank K ↥V ∧ r < d ∧
      (∀ u ∈ V₁, (∀ i, ∃ c : k, u i = algebraMap k K c) → u = 0) ∧
      LinearIndependent k w ∧ (∀ j, w j ∈ V₁) ∧ (∀ j i, w j i ∈ E) := by
  sorry

end DiazModulus
