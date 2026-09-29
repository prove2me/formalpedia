-- Prove2me | Theorems.Thm_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply
-- name    : AutomorphicForm.RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/fa69ec52-205b-54a2-984f-f887ef8d23ad
-- title:
--   Smoothness and uniform derivative bounds for the real Iwasawa rotation factor
-- statement:
--   Let $g$ be a $2\times 2$ real matrix with $\det g \neq 0$, and consider, for $x \in \mathbb{R}$, the matrix-valued function
--   $$k(x) \;=\; \bigl(\sqrt{(g_{00}+x g_{10})^2 + (g_{01}+x g_{11})^2}\bigr)^{-1}\begin{pmatrix} g_{01}+x g_{11} & -(g_{00}+x g_{10})\\ g_{00}+x g_{10} & g_{01}+x g_{11}\end{pmatrix},$$
--   the inverse being the real inverse of the square root (so the scalar factor would be $0$ where the square root vanishes, which under the hypothesis $\det g \neq 0$ does not occur). The assertion is a conjunction. First, for each pair of indices $i, j \in \{0,1\}$ the scalar function $x \mapsto k(x)_{ij}$ is $C^\infty$ on $\mathbb{R}$ (smoothness of order $\infty$ in the `ContDiff` sense). Second, for every natural number $n$ there exists a real constant $C > 0$ such that for all $i, j \in \{0,1\}$ and all $u \in \mathbb{R}$ the $n$-th iterated Fréchet derivative of $x \mapsto k(x)_{ij}$, evaluated at $u$, has norm at most $C$; thus the bound is uniform in the point $u$ and in the entry $(i,j)$, and depends only on $n$ and $g$.
--
--   The matrix $k(x)$ is the orthogonal factor in the real Iwasawa decomposition of $w\,n(x)\,g$, where $w$ is the Weyl element and $n(x)$ the upper unipotent, so this is the statement that the rotation angle $\theta(g,x)$ depends smoothly on $x$ with all derivatives bounded uniformly on $\mathbb{R}$. It feeds the polynomial-decay estimates for the weight Fourier integral and for unipotent Weyl integrals of unitary matrix coefficients at the real place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean

import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ContDiff

theorem AutomorphicForm.RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C := by sorry
