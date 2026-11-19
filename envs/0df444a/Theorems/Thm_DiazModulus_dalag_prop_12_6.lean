-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_6
-- name    : DiazModulus.dalag_prop_12_6
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:55.79863+00:00
-- url     : https://prove2.me/theorems/58147bd5-0a24-41fb-b81f-a5dcf1f2a677
-- title:
--   Waldschmidt 2000 (DALAG), Prop. 12.6, n < d not needed: if E has Property (A B; C 0), V ⊂ K^d has dim n, Y ⊂ V ∩ E^d finite-dim, then ℓ′ ≤ d − d′ ≤ n for some S rational over k
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A matrix $M$ with $s$ rows, $t$ columns and entries in $K$ *has the block form (A B; C 0) over $k$* if there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that, with $P$ and $Q$ read in $K$, the matrix $N = PMQ$ has $N_{ij} = 0$ whenever $i > r$ and $j > r$ (rows and columns numbered from $1$) and its upper left $r \times r$ block $A$ is invertible: $PMQ = \begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ regular, or empty when $r = 0$. A $k$-vector subspace $E$ of $K$ has *Property (A B; C 0)* (DALAG §12.1.3) if every non-zero matrix with entries in $E$ has the block form (A B; C 0) over $k$.
--
--   Let $E \subseteq K$ be a $k$-vector subspace with Property (A B; C 0). Let $V \subseteq K^d$ be a $K$-vector subspace, $n = \dim_K V$, and let $Y \subseteq V \cap E^d$ be a finite-dimensional $k$-vector subspace. Then there is a $K$-vector subspace $S \subseteq K^d$, rational over $k$ (spanned over $K$ by the vectors of $S$ whose coordinates all lie in $k$), such that, with $d' = \dim_K(K^d/S)$ and $\ell' = \dim_k\big(Y/(Y \cap S)\big)$,
--   $$\ell' \le d - d' \le n.$$
--   No hypothesis $n < d$ is made.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.6 (p. 425), in the integer form ℓ′ ≤ d − d′ ≤ n; the equivalent printed form with ratios is not stated. The printed hypothesis n < d is not used by the proof ("1 ≤ r ≤ n < d" only records it) and is dropped; for n = d the conclusion holds anyway with S = K^d. The space S, printed as an intersection of hyperplanes, is taken as the span of the leading r columns of P⁻¹, which is the same space. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_6 {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hE : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    {d : ℕ} (V : Submodule K (Fin d → K)) (Y : Submodule k (Fin d → K)) [FiniteDimensional k ↥Y]
    (hY : Y ≤ V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E)) :
    ∃ S : Submodule K (Fin d → K),
      Submodule.span K {v : Fin d → K | v ∈ S ∧ ∀ i, ∃ c : k, v i = algebraMap k K c} = S ∧
      Module.finrank k (↥Y ⧸ (S.restrictScalars k).comap Y.subtype) ≤
        d - Module.finrank K ((Fin d → K) ⧸ S) ∧
      d - Module.finrank K ((Fin d → K) ⧸ S) ≤ Module.finrank K ↥V := by
  sorry

end DiazModulus
