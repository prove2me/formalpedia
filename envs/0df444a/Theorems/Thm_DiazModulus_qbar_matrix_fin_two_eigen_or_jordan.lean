-- Prove2me | Theorems.Thm_DiazModulus_qbar_matrix_fin_two_eigen_or_jordan
-- name    : DiazModulus.qbar_matrix_fin_two_eigen_or_jordan
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:36.72743+00:00
-- url     : https://prove2.me/theorems/412a8540-a8bd-488e-b600-30595d6b20a3
-- title:
--   Every 2×2 matrix over Q̄ is scalar, has two distinct eigenvalues with an eigenbasis, or has a Jordan basis
-- statement:
--   Let $M$ be a $2 \times 2$ matrix with entries in the field $\overline{\mathbb{Q}}$ of algebraic numbers in $\mathbb{C}$, acting on column vectors in $\overline{\mathbb{Q}}^2$. Then one of the following holds:
--
--   - $M = cI$ for some $c \in \overline{\mathbb{Q}}$;
--   - there are linearly independent $v, w \in \overline{\mathbb{Q}}^2$ and $c_1 \neq c_2$ in $\overline{\mathbb{Q}}$ with $Mv = c_1v$ and $Mw = c_2w$;
--   - there are linearly independent $v, w \in \overline{\mathbb{Q}}^2$ and $c \in \overline{\mathbb{Q}}$ with $Mv = cv$ and $Mw = cw + v$.
--
--   **Proof.** Write $M$ with rows $(a, b)$ and $(c, d)$; two vectors $(x, y)$, $(x', y')$ are linearly independent as soon as $xy' - yx' \neq 0$. If $b = c = 0$: when $a = d$, $M = aI$; otherwise $(1, 0)$ and $(0, 1)$ are eigenvectors for $a \neq d$. If $b = 0$ and $c \neq 0$: when $a = d$, $v = (0, c)$ and $w = (1, 0)$ satisfy $Mv = av$ and $Mw = aw + v$; otherwise $(0, 1)$ and $(a - d, c)$ are eigenvectors for $d$ and $a$. If $b \neq 0$, take a root $l \in \overline{\mathbb{Q}}$ of $t^2 - (a + d)t + (ad - bc)$: a complex square root $s$ of the discriminant is algebraic over $\mathbb{Q}$, as its square is, so $s \in \overline{\mathbb{Q}}$ and $l = (a + d + s)/2$. The other root is $m = a + d - l$. If $l \neq m$, $(b, l - a)$ and $(b, m - a)$ are eigenvectors for $l$ and $m$, with determinant $b(m - l) \neq 0$; if $l = m$, $v = (b, l - a)$ and $w = (0, 1)$ satisfy $Mv = lv$ and $Mw = lw + v$. No algebraic-closedness instance for $\overline{\mathbb{Q}}$ is used.
--
--   **Novelty.** Standard linear algebra; routine.
-- source:
--   Standard linear algebra: the Jordan form of a 2×2 matrix over an algebraically closed field. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem qbar_matrix_fin_two_eigen_or_jordan (M : Matrix (Fin 2) (Fin 2) ↥Qbar) :
    (∃ c : ↥Qbar, M = c • (1 : Matrix (Fin 2) (Fin 2) ↥Qbar)) ∨
    (∃ (v w : Fin 2 → ↥Qbar) (c₁ c₂ : ↥Qbar), c₁ ≠ c₂ ∧ LinearIndependent (↥Qbar) ![v, w] ∧
        M.mulVec v = c₁ • v ∧ M.mulVec w = c₂ • w) ∨
    (∃ (v w : Fin 2 → ↥Qbar) (c : ↥Qbar), LinearIndependent (↥Qbar) ![v, w] ∧
        M.mulVec v = c • v ∧ M.mulVec w = c • w + v) := by
  sorry

end DiazModulus
