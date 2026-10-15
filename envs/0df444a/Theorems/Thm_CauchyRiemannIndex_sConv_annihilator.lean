-- Prove2me | Theorems.Thm_CauchyRiemannIndex_sConv_annihilator
-- name    : CauchyRiemannIndex.sConv_annihilator
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:02:02.117444+00:00
-- url     : https://prove2.me/theorems/4a317a3a-c60a-4435-b7b5-d93ad4cfb854
-- title:
--   Convolution in the $s$-variable preserves $L^q$ maps orthogonal to the image of a translation-invariant Cauchy–Riemann operator on the cylinder
-- statement:
--   Let $S_\infty$ be a continuous loop of $2n\times2n$ matrices, $D=\partial_s+J_0\partial_t+S_\infty(t)$, $1\le q\le\infty$, and let $g\in L^q(\mathbb R\times S^1,\mathbb R^{2n})$ satisfy
--   $$\int_{\mathbb R\times S^1}\langle Du,\ g\rangle=0$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$. Let $\rho\in C^\infty_c(\mathbb R)$ and
--   $$G(s,t)=\int_{\mathbb R}\rho(\sigma)\,g(s-\sigma,t)\,d\sigma .$$
--   Then $G\in L^q(\mathbb R\times S^1)$ and $\int\langle Du,G\rangle=0$ for every such $u$.
--
--   So the space of $L^q$ weak solutions of the formal adjoint equation $-\partial_s g+J_0\partial_t g+S_\infty^{T}g=0$ is closed under convolution in the translation direction $s$. This lets one regularize such solutions in $s$ while keeping the equation.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$, and $L^q(\mathbb R\times S^1)$ is `LpCyl n q`, i.e. $L^q$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`), with values in $\mathbb R^{2n}$ = `Vec n`. The convolution is written pointwise, `fun x => ∫ σ, ρ σ • g (x.1 - σ, x.2)`, with `g` the chosen representative of the $L^q$ class; $\rho$ is `ContDiff ℝ ∞` with `HasCompactSupport`. $q$ is in `ℝ≥0∞` with `Fact (1 ≤ q)`. Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$) and the operator is `crOp` with $S(s,t)=S_\infty(t)$. $S_\infty$ is only assumed continuous. The first conclusion is `MemLp G q cylMeasure`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞` be a continuous loop of matrices, `D = ∂ₛ + J₀ ∂ₜ + S∞(t)`, and `g ∈ L^q` of the
cylinder with `∫ ⟨D u, g⟩ = 0` for every test section `u`. For a smooth compactly supported
`ρ : ℝ → ℝ`, the convolution of `g` with `ρ` in the `s`-variable,
`G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ`, lies in `L^q` and again satisfies `∫ ⟨D u, G⟩ = 0` for every
test section `u`. -/
theorem sConv_annihilator (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (Sinf : ℝ → Mat n)
    (hc : Continuous Sinf) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    MemLp (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) q cylMeasure ∧
      ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
        ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x)
          (∫ σ, ρ σ • g (x.1 - σ, x.2)) ∂cylMeasure = 0 := by
  sorry

end CauchyRiemannIndex
