-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply
-- name    : AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/73091658-5b40-5ec1-ba79-ce1b54ede0dc
-- title:
--   Smoothness and bounded derivatives of the Iwasawa compact factor
-- statement:
--   Let $g$ be a $2\times 2$ matrix over $\mathbb{C}$ with $\det g \neq 0$. For $z \in \mathbb{C}$ set $P(z) = g_{00} + z\,g_{10}$ and $Q(z) = g_{01} + z\,g_{11}$ (the functions `botP` and `botQ`), put $r(z) = \sqrt{|P(z)|^{2} + |Q(z)|^{2}} \in \mathbb{R}$ (the function `radC`, defined via `Complex.normSq`), and let `kC` be the matrix $$\begin{pmatrix} \overline{Q(z)}/r(z) & -\overline{P(z)}/r(z) \\ P(z)/r(z) & Q(z)/r(z)\end{pmatrix},$$ with $r(z)$ coerced into $\mathbb{C}$. Viewing $\mathbb{C}$ as a normed real vector space, the theorem asserts two things. First, for each pair of indices $i, j \in \{0,1\}$ the entry function $w \mapsto (\mathrm{kC}\,g\,w)_{ij}$ is $C^{\infty}$ as a map of real normed spaces $\mathbb{C} \to \mathbb{C}$. Second, for every $n \in \mathbb{N}$ there is a real constant $C > 0$ — depending on $g$ and $n$ but uniform in the indices and the point — such that the $n$-th iterated real Fréchet derivative satisfies $\|D^{n}\bigl((\mathrm{kC}\,g\,\cdot)_{ij}\bigr)(z)\| \le C$ for all $i, j \in \{0,1\}$ and all $z \in \mathbb{C}$.
--
--   The matrix `kC` is the compact (special unitary) factor in the Iwasawa decomposition of $w\,n(z)\,g$ over $\mathbb{C}$, where $w$ is the Weyl element and $n(z)$ the upper unipotent matrix; the hypothesis $\det g \neq 0$ keeps $r$ bounded away from zero, which is what makes the entries smooth with derivatives bounded on all of $\mathbb{C}$. The estimate feeds the bounds on the associated $\mathbb{C}$-power factors and, through them, the polynomial decay estimates for the weight Fourier integrals and for unipotent Weyl-element integrals of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => kC g w i j)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
        ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by sorry
