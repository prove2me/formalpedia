-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
-- name    : AutomorphicForm.ComplexIwasawa.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ce25c089-0cc5-5cd7-bcb5-d6bae13db4d3
-- title:
--   Uniform derivative bounds for the compact Iwasawa factor on compacta
-- statement:
--   Fix a set $\mathcal G$ of complex $2\times 2$ matrices that is compact, such that $\det g \neq 0$ for every $g \in \mathcal G$, and fix $n \in \mathbb{N}$. Then there is a real constant $C > 0$ such that for every $g \in \mathcal G$, every pair of indices $i, j \in \{0,1\}$ and every $z \in \mathbb{C}$ one has $\bigl\| D^n_{\mathbb{R}}\bigl(w \mapsto (k_C(g,w))_{ij}\bigr)(z)\bigr\| \le C$, the derivative being the $n$-th iterated Fréchet derivative over $\mathbb{R}$ of the entry function on $\mathbb{C}$ viewed as a real normed space, and its norm that of an $n$-linear map. Here, writing $P_g(z) = g_{00} + z\,g_{10}$, $Q_g(z) = g_{01} + z\,g_{11}$ and $r_g(z) = \sqrt{|P_g(z)|^2 + |Q_g(z)|^2}$, the matrix $k_C(g,z)$ is $$\begin{pmatrix} \overline{Q_g(z)}/r_g(z) & -\overline{P_g(z)}/r_g(z) \\ P_g(z)/r_g(z) & Q_g(z)/r_g(z)\end{pmatrix}.$$ The constant $C$ depends on $\mathcal G$ and $n$ only, uniformly in $g$, in the entry indices and in the point $z$. The conclusion is a bound on the iterated derivative operator, which is defined for arbitrary functions; smoothness of the entries is not part of the assertion.
--
--   This is the uniform-in-$g$ form of the elementary bounds on the $SU(2)$-factor of the complex Iwasawa decomposition: all real derivatives of the entries of $k_C(g,\cdot)$ are bounded on all of $\mathbb{C}$ by a single constant as $g$ ranges over a compact set of invertible matrices. It feeds the corresponding uniform bounds for the derivatives of the powers $r_g^{-s}$ used in the archimedean estimates for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by sorry
