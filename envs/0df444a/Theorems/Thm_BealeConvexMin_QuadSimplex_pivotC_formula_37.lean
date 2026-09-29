-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_pivotC_formula_37
-- name    : BealeConvexMin.QuadSimplex.pivotC_formula_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:32:23.592007+00:00
-- url     : https://prove2.me/theorems/669bf384-ee15-4c52-a033-ab859c3a0b79
-- title:
--   Eq. (3.7) — closed form, symmetry and invariance of the transformed $(c_{kl})$
-- statement:
--   Let $(c_{kl})_{k,l=0}^{N}$ be the coefficient matrix of $C=\sum_{k,l}c_{kl}z_kz_l$ ($z_0=1$), let the new nonbasic variable $z_q=d_0+\sum_{l\ge1}d_lz_l$ replace $z_p$ and be stored in slot $p$, and let $e$ be given by (3.4) and $(c''_{kl})$ by (3.5)–(3.6). Then, writing $q$ for the new variable's slot,
--   $$
--   \begin{aligned}
--   c''_{qq}&=c_{pp}e_q^2,\\
--   c''_{ql}&=c_{pl}e_q+c_{pp}e_qe_l,\\
--   c''_{kq}&=c_{kp}e_q+c_{pp}e_ke_q,\\
--   c''_{kl}&=c_{kl}+c_{kp}e_l+c_{pl}e_k+c_{pp}e_ke_l,
--   \end{aligned}\qquad k,l\neq q. \tag{3.7}
--   $$
--   Moreover:
--   1. if $(c_{kl})$ is symmetric, so is $(c''_{kl})$;
--   2. $(c''_{kl})$ is the transformed matrix: substituting $z_p=\sum_l e_lz'_l$ (with $z'_l=z_l$ for $l\neq p$ and $z'_p$ the new variable) into $\sum_{k,l}c_{kl}z_kz_l$ gives $\sum_{k,l}c''_{kl}z'_kz'_l$.
--
--   This closed form is what the two lemmas on free variables are read from, and symmetry is what keeps "$c_{k0}$" meaning half the linear coefficient of $z_k$ throughout the iteration.
--
--   **Formalization Note** The new variable's slot is $p$, so "$k,l\neq q$" reads "$k,l\neq p$" and includes the index $0$. The identities are algebraic and hold for every $d$; the invariance is stated for every $z'$, the homogeneous form of the paper's identity with $z_0=1$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 176 (PDF p. 4), eq. (3.7) and the sentence after it

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 176, eq. (3.7) and the sentence after it. With `e = pivotE d p` (eq. (3.4))
and the new variable `z_q` stored in slot `p` (so the paper's `q` is `p` here and "`k, l ≠ q`"
reads "`k, l ≠ p`", index `0` included), the matrix `(c''_kl) = pivotC c p d` computed from (3.5)
and (3.6) satisfies (3.7); it is symmetric when `(c_kl)` is; and it is the transformed `(c_kl)`:
substituting `z_p = Σ_l e_l z'_l` into `C = Σ c_kl z_k z_l` gives `Σ c''_kl z'_k z'_l`. -/
theorem pivotC_formula_37 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) :
    let e := pivotE d p
    pivotC c p d p p = c p p * e p ^ 2 ∧
    (∀ l, l ≠ p → pivotC c p d p l = c p l * e p + c p p * e p * e l) ∧
    (∀ k, k ≠ p → pivotC c p d k p = c k p * e p + c p p * e k * e p) ∧
    (∀ k l, k ≠ p → l ≠ p →
      pivotC c p d k l = c k l + c k p * e l + c p l * e k + c p p * e k * e l) ∧
    (c.IsSymm → (pivotC c p d).IsSymm) ∧
    ∀ z' : Fin (N + 1) → ℝ,
      quadValue c (Function.update z' p (∑ l, e l * z' l)) = quadValue (pivotC c p d) z' := by sorry

end BealeConvexMin.QuadSimplex
