-- Prove2me | Theorems.Thm_CauchyRiemannIndex_sConv_annihilator_bounded
-- name    : CauchyRiemannIndex.sConv_annihilator_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:01:56.290137+00:00
-- url     : https://prove2.me/theorems/746ec9d2-499f-4a9b-b9a4-214abdb49a51
-- title:
--   The $s$-convolution of an $L^q$ map orthogonal to the image of a nondegenerate translation-invariant Cauchy–Riemann operator is essentially bounded
-- statement:
--   Let $S_\infty$ be a continuous loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate, $D=\partial_s+J_0\partial_t+S_\infty(t)$, $1\le q\le\infty$, and let $g\in L^q(\mathbb R\times S^1,\mathbb R^{2n})$ satisfy
--   $$\int_{\mathbb R\times S^1}\langle Du,\ g\rangle=0$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$. For $\rho\in C^\infty_c(\mathbb R)$ the function
--   $$G(s,t)=\int_{\mathbb R}\rho(\sigma)\,g(s-\sigma,t)\,d\sigma$$
--   is essentially bounded on $\mathbb R\times S^1$.
--
--   This is a regularity statement for $L^q$ weak solutions of the formal adjoint equation $-\partial_s g+J_0\partial_t g+S_\infty g=0$: after averaging in the translation direction $s$ they lie in $L^\infty$, for every exponent $q\ge1$.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$, and $L^q(\mathbb R\times S^1)$ is `LpCyl n q`, i.e. $L^q$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`), with values in $\mathbb R^{2n}$ = `Vec n`. The convolution is written pointwise, `fun x => ∫ σ, ρ σ • g (x.1 - σ, x.2)`, with `g` the chosen representative of the $L^q$ class; $\rho$ is `ContDiff ℝ ∞` with `HasCompactSupport`. $q$ is in `ℝ≥0∞` with `Fact (1 ≤ q)`. Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$) and the operator is `crOp` with $S(s,t)=S_\infty(t)$. `IsSymLoop` is continuity, $1$-periodicity and symmetry of $S_\infty(t)$; nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). The conclusion is `∃ C : ℝ, ∀ᵐ x ∂cylMeasure, ‖G x‖ ≤ C`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞` be a nondegenerate loop of symmetric matrices, `D = ∂ₛ + J₀ ∂ₜ + S∞(t)`, and
`g ∈ L^q` of the cylinder (`1 ≤ q ≤ ∞`) with `∫ ⟨D u, g⟩ = 0` for every test section `u`. For a
smooth compactly supported `ρ : ℝ → ℝ`, the convolution of `g` with `ρ` in the `s`-variable,
`G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ`, is essentially bounded on the cylinder. -/
theorem sConv_annihilator_bounded (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (Sinf : ℝ → Mat n)
    (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∃ C : ℝ, ∀ᵐ x ∂cylMeasure, ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ ≤ C := by
  sorry

end CauchyRiemannIndex
