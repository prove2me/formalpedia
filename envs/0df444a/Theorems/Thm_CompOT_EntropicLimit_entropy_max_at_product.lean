-- Prove2me | Theorems.Thm_CompOT_EntropicLimit_entropy_max_at_product
-- name    : CompOT.EntropicLimit.entropy_max_at_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:28.431751+00:00
-- url     : https://prove2.me/theorems/14c6da53-edb7-4801-8c44-91b17871f259
-- title:
--   Proof of Proposition 4.1, p. 426 — a ⊗ b is the unique solution of min_{P ∈ U(a,b)} −H(P)
-- statement:
--   Let $a \in \Sigma_n$ and $b \in \Sigma_m$. The product coupling $a \otimes b = ab^\top = (a_i b_j)_{i,j}$ lies in $U(a,b)$ and is the unique solution of
--   $$\min_{P \in U(a,b)} -\mathbf H(P):$$
--   every other $Q \in U(a,b)$ satisfies $\mathbf H(Q) < \mathbf H(a\otimes b)$.
--
--   This identifies the limit of $P_\varepsilon$ as $\varepsilon \to +\infty$ in Proposition 4.1: the coupling of maximal entropy between two prescribed marginals is the law of two independent random variables.
--
--   **Formalization Note** $\mathbf H$ uses $0\log 0 = 0$; indices are 0-based.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 4.1, p. 426 (last display)

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicLimit

/-- Proof of Proposition 4.1, p. 426: for `a ∈ Σ_n`, `b ∈ Σ_m`, the solution of
`min_{P ∈ U(a,b)} -H(P)` is `a ⊗ b = (a_i b_j)_{i,j}`: it lies in `U(a,b)` and every other
coupling has strictly smaller entropy. -/
theorem entropy_max_at_product {n m : ℕ}
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (Matrix.of fun i j => a i * b j) ∈ CompOT.Assignment.couplings a b ∧
      ∀ Q ∈ CompOT.Assignment.couplings a b, Q ≠ (Matrix.of fun i j => a i * b j) →
        entropy Q < entropy (Matrix.of fun i j => a i * b j) := by sorry

end CompOT.EntropicLimit
