-- Prove2me | Theorems.Thm_AffinePolicies_Simplex_Qmat_inv_mulVec_eq_weights
-- name    : AffinePolicies.Simplex.Qmat_inv_mulVec_eq_weights
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:16.247653+00:00
-- url     : https://prove2.me/theorems/c1524e56-dc44-4e41-adea-4a928413b2fa
-- title:
--   Theorem 1, proof, PDF p. 6 — Q⁻¹(b − b^{m+1}) = α: the convex multipliers are affine in b
-- statement:
--   Let $b^1,\dots,b^{m+1}\in\mathbb R^m$ be affinely independent, let $Q$ be the matrix with columns $b^j-b^{m+1}$ ($j=1,\dots,m$), and let $\alpha_1,\dots,\alpha_{m+1}$ be real numbers with $\alpha_1+\cdots+\alpha_{m+1}=1$. If $b=\sum_{j=1}^{m+1}\alpha_j b^j$, then
--   $$Q^{-1}\big(b-b^{m+1}\big)=(\alpha_1,\dots,\alpha_m)^T.$$
--
--   In particular, the convex-combination multipliers of a point $b$ of the simplex $\operatorname{conv}(b^1,\dots,b^{m+1})$ are an affine function of $b$; this is what allows the optimal vertex decisions to be interpolated by an affine policy in Theorem 1.
--
--   **Formalization Note** The paper takes $\alpha_j\ge 0$ (a point of the simplex); nonnegativity is not used by the identity, so it is omitted, which makes the statement stronger. Indices are 0-based: $(\alpha_1,\dots,\alpha_m)$ is `fun j => α (Fin.castSucc j)`.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 1, proof, display Q⁻¹(b − b^{m+1}) = α, PDF p. 6

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.Simplex

open Matrix

theorem Qmat_inv_mulVec_eq_weights {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    (Qmat v)⁻¹ *ᵥ ((∑ j, α j • v j) - v (Fin.last m)) = fun j => α (Fin.castSucc j) := by sorry

end AffinePolicies.Simplex
