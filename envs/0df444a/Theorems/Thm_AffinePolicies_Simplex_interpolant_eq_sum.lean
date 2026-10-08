-- Prove2me | Theorems.Thm_AffinePolicies_Simplex_interpolant_eq_sum
-- name    : AffinePolicies.Simplex.interpolant_eq_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:27.296006+00:00
-- url     : https://prove2.me/theorems/724ef902-08ce-4716-b3a5-4838afa6c5d6
-- title:
--   Theorem 1, proof, PDF pp. 6–7 — ỹ(b) = YQ⁻¹(b − b^{m+1}) + y*(b^{m+1}) = Σⱼ αⱼ y*(bʲ)
-- statement:
--   Let $b^1,\dots,b^{m+1}\in\mathbb R^m$ be affinely independent, let $Q$ be the matrix with columns $b^j-b^{m+1}$, let $g:\mathbb R^m\to\mathbb R^{n_2}$ be any second-stage rule, and let $Y$ be the matrix with columns $g(b^j)-g(b^{m+1})$ ($j=1,\dots,m$), as in display (2). Define the affine interpolant
--   $$\tilde y(b)=YQ^{-1}\big(b-b^{m+1}\big)+g(b^{m+1}).$$
--   Then for all reals $\alpha_1,\dots,\alpha_{m+1}$ with $\sum_j\alpha_j=1$,
--   $$\tilde y\Big(\sum_{j=1}^{m+1}\alpha_j b^j\Big)=\sum_{j=1}^{m+1}\alpha_j\, g(b^j).$$
--
--   So the affine policy $\tilde y$ agrees with $g$ at every vertex of the simplex and, at any point of the simplex, equals the convex combination of the vertex decisions with the point's own multipliers. In the paper $g=y^*$ is an optimal second-stage solution.
--
--   **Formalization Note** The paper takes the multipliers in $[0,1]$; only $\sum_j\alpha_j=1$ is used, so nonnegativity is omitted (stronger statement). The rule $g$ is arbitrary.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 1, proof, (2) and the display defining ỹ(b), PDF pp. 6–7

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.Simplex

theorem interpolant_eq_sum {m n₂ : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) (g : (Fin m → ℝ) → Fin n₂ → ℝ)
    (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    interpolant v g (∑ j, α j • v j) = ∑ j, α j • g (v j) := by sorry

end AffinePolicies.Simplex
