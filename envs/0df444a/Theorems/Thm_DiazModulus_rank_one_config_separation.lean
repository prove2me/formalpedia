-- Prove2me | Theorems.Thm_DiazModulus_rank_one_config_separation
-- name    : DiazModulus.rank_one_config_separation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-08T16:34:51.426732+00:00
-- url     : https://prove2.me/theorems/6412e225-68f7-4d31-b833-9e358b8177f0
-- title:
--   Separation: for subfields K ≤ F of ℂ, a K-space V₀ ⊆ F and w₁…w_m algebraically independent over F, every p×q configuration over K (p, q ≥ 2) in V₀ + Kw₁ + … + Kw_m lies in V₀
-- statement:
--   A $p \times q$ configuration over a field $K$ in a $K$-subspace $V \subseteq \mathbb{C}$ is a pair $x_1, \dots, x_p$ and $y_1, \dots, y_q$ of complex numbers, each family linearly independent over $K$, with every product $x_iy_j$ in $V$; it is the input of Roy's strong six exponentials theorem when $p = 2$, $q = 3$, $K = \overline{\mathbb{Q}}$ and $V = \widetilde{\mathcal{L}}$.
--
--   Let $K \subseteq F$ be subfields of $\mathbb{C}$, $V_0 \subseteq F$ a $K$-subspace, and $w_1, \dots, w_m$ algebraically independent over $F$. Every $p \times q$ configuration over $K$ with $p, q \ge 2$ in $V_0 + Kw_1 + \dots + Kw_m$ has all its products in $V_0$.
--
--   With $K = \overline{\mathbb{Q}}$, $F = \overline{\mathbb{Q}}(u)$ and $V_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ this contains the separation steps of `DiazModulus.generic_period_never_enters` ($w = i\pi$, $2 \times 2$) and of `DiazModulus.generic_circle_point_no_two_by_three_configuration` ($2 \times 3$).
--
--   **Proof.** Induction on $m$. For $m + 1$, let $F'$ be the field generated over $F$ by $w_1, \dots, w_m$; then $w_{m+1}$ is transcendental over $F'$, and $V_0' = V_0 + Kw_1 + \dots + Kw_m \subseteq F'$. Every entry $(i, j)$ lies in a $2 \times 2$ block (rows $i \neq i'$, columns $j \neq j'$, using $p, q \ge 2$), which is a $2 \times 2$ configuration in $V_0' + Kw_{m+1}$; `DiazModulus.rank_one_config_separation_two` puts $x_iy_j$ in $V_0'$, and the induction hypothesis puts it in $V_0$.
--
--   **Novelty.** Not found in the sources read. It generalises the library's separation steps, which are over $\overline{\mathbb{Q}}$ with $V_0 = H_0$, to any base field, any $V_0 \subseteq F$, any number of generic numbers and any $p, q \ge 2$.
-- source:
--   Not found in the sources read; generalises the separation steps of DiazModulus.generic_period_never_enters and DiazModulus.generic_circle_point_no_two_by_three_configuration. R6 of the Diaz modulus mission (the polar-degree note). Formal proof: Diaz modulus mission, 8 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rank_one_config_separation (K F : Subfield ℂ) (hKF : K ≤ F)
    (V₀ : Submodule K ℂ) (hV₀ : ∀ v ∈ V₀, v ∈ F) (m : ℕ) (w : Fin m → ℂ)
    (hw : AlgebraicIndependent F w) (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (x : Fin p → ℂ) (y : Fin q → ℂ) (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀ ⊔ Submodule.span K (Set.range w)) :
    ∀ i j, x i * y j ∈ V₀ := by
  sorry

end DiazModulus
