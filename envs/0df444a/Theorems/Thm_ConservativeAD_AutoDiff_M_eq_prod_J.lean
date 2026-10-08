-- Prove2me | Theorems.Thm_ConservativeAD_AutoDiff_M_eq_prod_J
-- name    : ConservativeAD.AutoDiff.M_eq_prod_J
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:42:15.698346+00:00
-- url     : https://prove2.me/theorems/3d8da4c5-c1eb-4478-8d87-bfdff0717d61
-- title:
--   Proof of Theorem 8 — $M_k=J_k\times J_{k-1}\times\cdots\times J_{p+1}\times J_p$
-- statement:
--   Fix an evaluation program and any family of vectors $d_k\in\mathbb R^{|\mathtt{parents}(k)|}$. Let $J_k=I-e_ke_k^T+e_k\tilde d_k^T$ ($\tilde d_k$ is $d_k$ lifted to $\mathbb R^q$), let $J_p\in\mathbb R^{q\times p}$ have ones at the positions $(i,i)$, $i\le p$, and let $M_k\in\mathbb R^{q\times p}$ have row $i$ equal to the forward-mode row $\partial x_i/\partial x_{1,\dots,p}$ of Algorithm 2 for $i\le k$ and $0$ for $i>k$. Then for every non-input node $k$,
--
--   $$
--   M_k=J_k\times J_{k-1}\times\cdots\times J_{p+1}\times J_p .
--   $$
--
--   Applied at $k=q$, the identity writes the output of forward mode as a product of matrices drawn from the conservative mappings $L_k$ of (10).
--
--   **Formalization Note** Nodes are 0-based; the product runs over the non-input nodes $j\le k$, largest first. The identity is algebraic and holds for every family $d$, not only for admissible choices.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), pp. 22–23, §5.2, proof of Theorem 8 (definition of M_k, p. 22; identity, p. 23)

import Mathlib
import Definitions.Def_ConservativeAD_AutoDiff_Program
import Definitions.Def_ConservativeAD_AutoDiff_ProofMatrices

namespace ConservativeAD.AutoDiff

/-- Proof of Theorem 8, p. 23: for every family `d` of vectors `d_k` and every non-input node `k`,
the matrix `M_k` (rows `∂x_i/∂x_{1,…,p}` of Algorithm 2 for `i ≤ k`, zero below) equals
`J_k × J_{k−1} × ⋯ × J_{p+1} × J_p`. -/
theorem M_eq_prod_J {p q : ℕ} (P : Program p q) (d : P.Choice) (k : Fin q) (hk : p ≤ k.val) :
    P.Mmat d k = P.jprod d k * Jp p q := by sorry

end ConservativeAD.AutoDiff
