-- Prove2me | Theorems.Thm_CauchyRiemannIndex_periodic_weak_solution_bound
-- name    : CauchyRiemannIndex.periodic_weak_solution_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:32:00.618784+00:00
-- url     : https://prove2.me/theorems/1c4b0660-85c5-4396-a4c6-e19fc66f7164
-- title:
--   $L^1\to L^\infty$ bound for weak periodic solutions of a nondegenerate asymptotic operator
-- statement:
--   Let $S_\infty:\mathbb R\to\mathbb R^{2n\times2n}$ be a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $A=-J_0\partial_t-S_\infty(t)$ is nondegenerate, and let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$. Then there is a constant $C$, depending only on $S_\infty$, with the following property. Let $\eta,f:\mathbb R\to\mathbb R^{2n}$ be integrable on $[0,1)$, and suppose $\eta$ is a weak periodic solution of $J_0\eta'+S_\infty\eta=f$, that is,
--   $$\int_0^1\big\langle J_0\psi'(t)+S_\infty(t)\psi(t),\ \eta(t)\big\rangle\,dt=\int_0^1\big\langle\psi(t),\ f(t)\big\rangle\,dt$$
--   for every smooth $1$-periodic $\psi:\mathbb R\to\mathbb R^{2n}$. Then
--   $$|\eta(t)|\le C\int_0^1|f(\tau)|\,d\tau\qquad\text{for almost every }t\in[0,1).$$
--
--   This is an $L^1\to L^\infty$ estimate for the periodic problem of the asymptotic operator (Wendl (3.10)). It is applied to the slices $t\mapsto u(s,t)$ of maps on the cylinder $\mathbb R\times S^1$ in the analysis of the translation-invariant Cauchy–Riemann operator $\partial_s+J_0\partial_t+S_\infty(t)$ (Wendl, Theorem 4.11).
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, $J_0$ is `Matrix.J`, and matrices act through `Matrix.toEuclideanLin`. The loop is `IsSymLoop` (continuous, $1$-periodic, symmetric values); nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). Integrals over $[0,1)$ are Bochner integrals for Lebesgue measure restricted to `Set.Ico 0 1`, $\psi'$ is `deriv ψ`, and the conclusion is an almost-everywhere statement for that restricted measure. The constant $C$ is chosen before $\eta$ and $f$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, (3.10) (asymptotic operators) and Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞` be a nondegenerate loop of symmetric matrices. There is a constant `C` with the
following property. If `η, f : ℝ → ℝ²ⁿ` are integrable on `[0, 1)` and `η` is a weak periodic
solution of `J₀ η' + S∞(t) η = f`, meaning that
`∫₀¹ ⟨J₀ ψ' + S∞ ψ, η⟩ dt = ∫₀¹ ⟨ψ, f⟩ dt` for every smooth `1`-periodic `ψ : ℝ → ℝ²ⁿ`, then
`|η(t)| ≤ C ∫₀¹ |f|` for almost every `t ∈ [0, 1)`.

This is an `L¹ → L^∞` bound for the periodic problem of the asymptotic operator
`-J₀ ∂ₜ - S∞`, used for slices `t ↦ u(s, t)` of sections of the cylinder. -/
theorem periodic_weak_solution_bound (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ, ∀ η f : ℝ → Vec n, IntegrableOn η (Set.Ico 0 1) → IntegrableOn f (Set.Ico 0 1) →
      (∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)) →
      ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)), ‖η t‖ ≤ C * ∫ t in Set.Ico (0 : ℝ) 1, ‖f t‖ := by
  sorry

end CauchyRiemannIndex
