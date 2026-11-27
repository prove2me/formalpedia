-- Prove2me | Theorems.Thm_AbelianCayleyHDX_maximal_minors_linearIndependent_of_oneGeneric
-- name    : AbelianCayleyHDX.maximal_minors_linearIndependent_of_oneGeneric
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T00:33:52.651167+00:00
-- url     : https://prove2.me/theorems/ee2494a1-a15b-49df-a396-77aeb4f15c92
-- title:
--   Maximal minors of a 1-generic matrix of linear forms are linearly independent (Eisenbud)
-- statement:
--   Let $K$ be an algebraically closed field and let $M=(M_{ij})$ be a $k\times m$ matrix, $k\le m$, of linear forms $M_{ij}=\sum_{r}A_{ijr}X_r$ in the polynomial ring $K[X_1,\dots,X_t]$. Call $M$ **1-generic** if every generalized entry
--   $$\sum_{i,j}\alpha_i\beta_jM_{ij},\qquad 0\ne\alpha\in K^k,\ 0\ne\beta\in K^m,$$
--   is a nonzero linear form. Then the $\binom mk$ maximal minors of $M$ are linearly independent over $K$.
--
--   This follows from Eisenbud's theorem that the ideal of maximal minors of a 1-generic matrix has the expected height $m-k+1$ (Theorem 6.4). By Corollary A2.61, the maximal minors then form a minimal generating set of this ideal after localizing at the homogeneous maximal ideal, so no nontrivial linear relation among them exists. In the paper this is the "Polynomial independence" step of Proposition 4.6.
--
--   **Formalization Note** A linear form is identified with its coefficient vector $(A_{ijr})_r$, and 1-genericity says that the coefficient vector of each generalized entry is nonzero. Minors use the columns $J\subseteq\{1,\dots,m\}$, $|J|=k$, in increasing order.
-- source:
--   David Eisenbud, The Geometry of Syzygies, GTM 229 (2005), Theorem 6.4 and Corollary A2.61; as used in Mao, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Proposition 4.6, p.17

import Mathlib

namespace AbelianCayleyHDX

/-- **Maximal minors of a 1-generic matrix of linear forms are linearly independent**
(Eisenbud, *The Geometry of Syzygies*, GTM 229, Theorem 6.4 and Corollary A2.61; used in Mao,
*Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held
version, sha256 6f5b0daa…75ba), proof of Proposition 4.6, p.17). Let `K` be algebraically closed and
let `M = (Mᵢⱼ)` be a `k × m` matrix (`k ≤ m`) of linear forms `Mᵢⱼ = ∑_r Aᵢⱼᵣ X_r` in
`K[X_1, …, X_t]`. If `M` is 1-generic — every generalized entry `∑ αᵢ βⱼ Mᵢⱼ` with `α ≠ 0`, `β ≠ 0`
is a nonzero linear form — then its `binom(m, k)` maximal minors are linearly independent over `K`.

**Formalization Note** A linear form is identified with its coefficient vector; 1-genericity
says the coefficient vector `(∑ αᵢ βⱼ Aᵢⱼᵣ)_r` is nonzero. -/
theorem maximal_minors_linearIndependent_of_oneGeneric (K : Type*) [Field K] [IsAlgClosed K]
    {t k m : ℕ} (hkm : k ≤ m) (A : Fin k → Fin m → Fin t → K)
    (hgen : ∀ (α : Fin k → K) (β : Fin m → K), α ≠ 0 → β ≠ 0 →
      ∃ r, ∑ i, ∑ l, α i * β l * A i l r ≠ 0) :
    LinearIndependent K (fun J : {J : Finset (Fin m) // J.card = k} =>
      (Matrix.of fun i l => ∑ r : Fin t,
        MvPolynomial.C (A i (J.1.orderEmbOfFin J.2 l) r) * MvPolynomial.X r).det) := by sorry

end AbelianCayleyHDX
