-- Prove2me | Theorems.Thm_Diaz_no_vanishing_coeff
-- name    : Diaz.no_vanishing_coeff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:20.927201+00:00
-- url     : https://prove2.me/theorems/d89116c8-0be1-450e-acdc-311e11fc6cbc
-- title:
--   No vanishing coefficient: $w^{\mathsf{T}} H v \neq 0$ for non-zero $w, v$ over the base field
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $u, r \in \mathbb{C}$ with
--
--   $$r \in K, \qquad u \notin K, \qquad u\bar u = r^{2}.$$
--
--   Let $w = (w_0, w_1)$ and $v = (v_0, v_1)$ be non-zero vectors in $\mathbb{C}^{2}$ all of whose entries lie in $K$. Then the bilinear coefficient of $H(u,r)$ at $(w,v)$ does not vanish:
--
--   $$w_0\,(u v_0 + r v_1)  +  w_1\,(r v_0 + \bar u v_1)  \neq  0.$$
--
--   **Why.** Because $\det H = 0$, the coefficient factors as a product of two linear forms,
--
--   $$w^{\mathsf{T}} H v = \Big(w_0 + \tfrac{r}{u} w_1\Big)\Big(u v_0 + r v_1\Big),$$
--
--   so if it vanished, one of the two factors would vanish — that is, a relation $u\alpha + r\beta = 0$ would hold with $\alpha, \beta \in K$ not both zero. Since $r \in K$ is non-zero, such a relation solves for $u$ inside $K$, contradicting $u \notin K$.
--
--   **Note what is not assumed.** Transcendence of $u$ plays no part: only $u \notin K$ is used. That is a strictly weaker hypothesis and it is all the argument needs.
--
--   **Role.** This is the second half of the tension around $H$: over $\mathbb{C}$ the rows of $H$ are dependent ($\det H = 0$), yet over $K$ no coefficient of the associated bilinear form vanishes. Dependent over $\mathbb{C}$, independent over $K$ — the configuration that places $H$ at the boundary of the Matrix Coefficient Conjecture, and the algebraic reason a coefficient-vanishing attack cannot separate a Diaz candidate from an ordinary point of the same circle.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Rigidity.lean#L60-L86

import Mathlib

open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

theorem Diaz.no_vanishing_coeff (hr : r ∈ K) (huK : u ∉ K)
    (h : u * conj u = r ^ 2)
    (w v : Fin 2 → ℂ) (hwK : ∀ i, w i ∈ K) (hvK : ∀ i, v i ∈ K)
    (hw : w ≠ 0) (hv : v ≠ 0) :
    w 0 * (u * v 0 + r * v 1) + w 1 * (r * v 0 + conj u * v 1) ≠ 0 := by sorry
