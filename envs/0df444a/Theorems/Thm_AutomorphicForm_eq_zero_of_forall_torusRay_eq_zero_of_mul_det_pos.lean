-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos
-- name    : AutomorphicForm.eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/51371f34-0428-5eb3-b2b1-e07b1331cd6f
-- title:
--   Vanishing on a torus ray kills a determinant component
-- statement:
--   Let $B : M_2(\mathbb{R}) \to \mathbb{C}$ be a function on real $2 \times 2$ matrices, and let $u, z : \mathbb{R} \to \mathbb{C}$ and $\chi : \mathtt{rowIsometrySubgroup₀}\ \mathbb{R} \to \mathbb{C}$ be arbitrary functions, where $\mathtt{rowIsometrySubgroup₀}\ \mathbb{R}$ is a subgroup of $\mathrm{GL}_2(\mathbb{R})$ (a variant of the subgroup `rowIsometrySubgroup` of row isometries, the invertible $k$ with $|\det k| = 1$ for which $x \mapsto (x,y) k$ preserves $\|x\|^2 + \|y\|^2$). Assume three quasi-invariance laws: for every $t \in \mathbb{R}$ and every $x$ with $\det x \neq 0$, $B(\begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix} x) = u(t) B(x)$; for every $t > 0$ and every $x$ with $\det x \neq 0$, $B(t \cdot x) = z(t) B(x)$; and for every $r$ in that subgroup and every $x \in \mathrm{GL}_2(\mathbb{R})$, $B(x r) = \chi(r) B(x)$, the argument being the underlying matrix. Let $\varepsilon \in \{1, -1\}$ and suppose $B$ vanishes along the corresponding torus ray, i.e. $B(\begin{pmatrix} \varepsilon \sqrt{y} & 0 \\ 0 & (\sqrt{y})^{-1} \end{pmatrix}) = 0$ for all $y > 0$. Then $B(x) = 0$ for every real $2 \times 2$ matrix $x$ with $\varepsilon \det x > 0$.
--
--   This is the Iwasawa decomposition of $\mathrm{GL}_2(\mathbb{R})$ in the form used for automorphic forms: a function transforming by scalars under left upper unipotents, positive scalars and right multiplication by the row-isometry subgroup is determined on each determinant-sign component by its values on the diagonal torus ray of that component. It is used in the proof that some Whittaker coefficient of an automorphic form at the identity is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos.lean

import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.eq_zero_of_forall_torusRay_eq_zero_of_mul_det_pos
    (B : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (u z : ℝ → ℂ) (χ : rowIsometrySubgroup₀ ℝ → ℂ)
    (hU : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (!![1, t; 0, 1] * x) = u t * B x)
    (hZ : ∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = z t * B x)
    (hK : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        χ r * B (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h0 : ∀ y : ℝ, 0 < y → B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < ε * x.det) :
    B x = 0 := by sorry
