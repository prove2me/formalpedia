-- Prove2me | Theorems.Thm_CauchyRiemannIndex_weak_identity_of_contDiff_one
-- name    : CauchyRiemannIndex.weak_identity_of_contDiff_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T20:47:25.052173+00:00
-- url     : https://prove2.me/theorems/21213c39-a66c-49c5-8234-fc303160fc23
-- title:
--   Weak periodic solutions of $J_0\eta'+S_\infty\eta=f$ may be tested against $C^1$ periodic functions
-- statement:
--   Let $S_\infty:\mathbb R\to\mathbb R^{2n\times2n}$ be continuous, let $J_0=\begin{pmatrix}0&-\mathrm{Id}\ \mathrm{Id}&0\end{pmatrix}$, and let $\eta,f:\mathbb R\to\mathbb R^{2n}$ be integrable on $[0,1)$. Suppose that
--   $$\int_0^1\big\langle J_0\psi'(t)+S_\infty(t)\psi(t),\ \eta(t)\big\rangle\,dt=\int_0^1\big\langle\psi(t),\ f(t)\big\rangle\,dt \tag{$*$}$$
--   for every smooth $1$-periodic $\psi:\mathbb R\to\mathbb R^{2n}$. Then $(*)$ holds for every continuously differentiable $1$-periodic $\psi:\mathbb R\to\mathbb R^{2n}$.
--
--   The identity $(*)$ says that $\eta$ is a weak periodic solution of $J_0\eta'+S_\infty\eta=f$, the periodic problem of the asymptotic operator $-J_0\partial_t-S_\infty$ (Wendl (3.10)). When $S_\infty$ is only continuous, periodic solutions of linear equations with coefficient $S_\infty$ are $C^1$ rather than smooth; this statement allows such functions in $(*)$.
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, $J_0$ is `Matrix.J`, and matrices act through `Matrix.toEuclideanLin`. Integrals over $[0,1)$ are Bochner integrals for Lebesgue measure restricted to `Set.Ico 0 1`, $\psi'$ is `deriv ψ`, smooth means `ContDiff ℝ ∞` and $C^1$ means `ContDiff ℝ 1`. Only continuity of $S_\infty$ is assumed.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, (3.10) (asymptotic operators) and Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞ : ℝ → ℝ^{2n×2n}` be continuous and let `η, f` be integrable on `[0, 1)`. If
`∫₀¹ ⟨J₀ ψ' + S∞ ψ, η⟩ = ∫₀¹ ⟨ψ, f⟩` holds for every smooth `1`-periodic `ψ : ℝ → ℝ²ⁿ`,
then it holds for every `C¹` `1`-periodic `ψ`. -/
theorem weak_identity_of_contDiff_one (n : ℕ) (Sinf : ℝ → Mat n) (hS : Continuous Sinf)
    (η f : ℝ → Vec n) (hη : IntegrableOn η (Set.Ico 0 1)) (hf : IntegrableOn f (Set.Ico 0 1))
    (hw : ∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)) :
    ∀ ψ : ℝ → Vec n, ContDiff ℝ 1 ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t) := by
  sorry

end CauchyRiemannIndex
