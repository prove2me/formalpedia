-- Prove2me | Theorems.Thm_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
-- name    : AutomorphicForm.apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/b2e975e9-d454-5ff8-9cdf-bb752c8e24ce
-- title:
--   Vanishing limit formula on GL₂(ℂ) at a scalar
-- statement:
--   Let $F$ be a complex-valued function of the entries of a $2\times 2$ complex matrix, regarded as a function on $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{C}$, which is $C^\infty$ as a function on the underlying real vector space and has compact support. Assume $F$ is invariant under conjugation by unitary matrices: for every $u$ in the unitary group of $2\times 2$ complex matrices and every matrix $E$, one has $F(u E u^{*}) = F(E)$, where $u^*$ is the conjugate transpose. Let $c \in \mathbb{C}$ with $c \neq 0$, and suppose there exists $\varepsilon > 0$ such that for every $w \in \mathbb{C}$ with $w \neq 0$ and $\|w\| < \varepsilon$ the integral over $v \in \mathbb{C}$, against the Lebesgue-type volume measure on $\mathbb{C}$, of $F\begin{pmatrix} c e^{w} & v \\ 0 & c e^{-w}\end{pmatrix}$ vanishes. The conclusion is that $F$ vanishes at the scalar matrix $\begin{pmatrix} c & 0 \\ 0 & c\end{pmatrix}$. (The passage between the function-of-two-indices form of the argument and matrices is via the equivalence `Matrix.of`.)
--
--   This is the vanishing form of Harish-Chandra's limit formula for $\mathrm{GL}_2(\mathbb{C})$, written along the upper-triangular slice: for $w \neq 0$ the matrices displayed sweep out the conjugacy class of the regular semisimple element $\mathrm{diag}(ce^{w}, ce^{-w})$, so the inner integral is the corresponding weighted orbital integral, and its limit as $w \to 0$ recovers the value of $F$ at the central element. It is used to pass from vanishing of orbital integrals at regular semisimple elements near a scalar to vanishing of the test function at that scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero.lean

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.apply_scalar_eq_zero_of_conj_unitary_eq_of_forall_integral_upperTriangular_complex_eq_zero
    (F : (Fin 2 → Fin 2 → ℂ) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hinv : ∀ u : Matrix (Fin 2) (Fin 2) ℂ, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ∀ E : Fin 2 → Fin 2 → ℂ, F (Matrix.of.symm (u * Matrix.of E * star u)) = F E)
    (c : ℂ) (hc : c ≠ 0)
    (hvan : ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε →
      ∫ v : ℂ, F (Matrix.of.symm !![c * Complex.exp w, v; 0, c * Complex.exp (-w)]) = 0) :
    F (Matrix.of.symm !![c, 0; 0, c]) = 0 := by sorry
