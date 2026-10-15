-- Prove2me | Theorems.Thm_CauchyRiemannIndex_crOp_energy_identity
-- name    : CauchyRiemannIndex.crOp_energy_identity
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T21:58:07.927616+00:00
-- url     : https://prove2.me/theorems/4fdf2b86-d1d8-428d-9584-a3bbcd0cad33
-- title:
--   $L^2$ identity for translation-invariant Cauchy–Riemann operators on the cylinder
-- statement:
--   Let $S_\infty:\mathbb R\to\mathbb R^{2n\times2n}$ be continuous with symmetric values. For every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$,
--   $$\int_{\mathbb R\times S^1}\big|\partial_s u+J_0\partial_t u+S_\infty(t)u\big|^2=\int_{\mathbb R\times S^1}|\partial_s u|^2+\int_{\mathbb R\times S^1}\big|J_0\partial_t u+S_\infty(t)u\big|^2 .$$
--   So the $L^2$ norm of $D=\partial_s+J_0\partial_t+S_\infty(t)$ splits into the $s$-derivative part and the part of the asymptotic operator $-J_0\partial_t-S_\infty$. It is a basic identity for translation-invariant Cauchy–Riemann operators on the cylinder (Wendl, Lecture 4).
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and integrals over $\mathbb R\times S^1$ are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The integrals are Bochner integrals over `cylMeasure` of squared Euclidean norms on `EuclideanSpace ℝ (Fin n ⊕ Fin n)`; $Du$ is `crOp` with $S(s,t)=S_\infty(t)$, $\partial_s,\partial_t$ are `partialS`, `partialT`, and $J_0$, $S_\infty(t)$ act through `Matrix.toEuclideanLin`. $S_\infty$ need not be periodic or nondegenerate.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞ : ℝ → ℝ^{2n×2n}` be continuous with symmetric values, and let `u` be a test
section of the cylinder `ℝ × S¹`. Then
`∫ |∂ₛu + J₀ ∂ₜu + S∞(t) u|² = ∫ |∂ₛu|² + ∫ |J₀ ∂ₜu + S∞(t) u|²`
over `ℝ × [0, 1)`.

So the `L²` norm of the translation-invariant Cauchy–Riemann operator `D = ∂ₛ + J₀ ∂ₜ + S∞(t)`
splits into the `s`-derivative part and the asymptotic operator part. -/
theorem crOp_energy_identity (n : ℕ) (Sinf : ℝ → Mat n) (hc : Continuous Sinf)
    (hsymm : ∀ t, (Sinf t).IsSymm) (u : ℝ × ℝ → Vec n) (hu : IsTestSection u) :
    ∫ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure +
        ∫ x, ‖Matrix.toEuclideanLin (J₀ n) (partialT u x) +
          Matrix.toEuclideanLin (Sinf x.2) (u x)‖ ^ 2 ∂cylMeasure := by
  sorry

end CauchyRiemannIndex
