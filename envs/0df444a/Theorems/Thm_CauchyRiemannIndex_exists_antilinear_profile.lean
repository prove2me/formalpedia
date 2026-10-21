-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_antilinear_profile
-- name    : CauchyRiemannIndex.exists_antilinear_profile
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T13:22:26.211006+00:00
-- url     : https://prove2.me/theorems/887019f2-aae2-4a09-9f27-461060235821
-- title:
--   Smooth functions on the cylinder with prescribed asymptotic loops e^{2πiat}, e^{2πibt} and |a − b| zeros in normal form
-- statement:
--   Let $a,b\in\mathbb{Z}$. There exist a smooth function $\beta:\mathbb{R}\times\mathbb{R}\to\mathbb{C}$, $1$-periodic in $t$ (so a function on the cylinder $\mathbb{R}\times S^1$), finite sets $Z^+,Z^-\subset\mathbb{R}\times[0,1)$ and a radius $r>0$ such that:
--
--   1. the derivative $d\beta$ is bounded on $\mathbb{R}\times\mathbb{R}$;
--   2. $\beta(s,t)\to e^{2\pi i a t}$ as $s\to+\infty$ and $\beta(s,t)\to e^{2\pi i b t}$ as $s\to-\infty$, uniformly in $t$, and there are $R$ and $c>0$ with $c\le|\beta(s,t)|\le 1/c$ whenever $|s|\ge R$;
--   3. $Z^+\cap Z^-=\emptyset$, and $\beta(x)=0$ if and only if $x=(\zeta_1,\zeta_2+m)$ for some $\zeta\in Z^+\cup Z^-$ and $m\in\mathbb{Z}$;
--   4. every $\zeta\in Z^+\cup Z^-$ satisfies $|\zeta_1|+r\le1$, and for $z\in\mathbb{C}$ with $|z|<r$ (identifying $z$ with $(\operatorname{Re}z,\operatorname{Im}z)$)
--   $$\beta(\zeta+z)=z\quad(\zeta\in Z^+),\qquad \beta(\zeta+z)=\bar z\quad(\zeta\in Z^-);$$
--   5. if $b\le a$ then $Z^-=\emptyset$ and $\#Z^+=a-b$; if $a\le b$ then $Z^+=\emptyset$ and $\#Z^-=b-a$.
--
--   This supplies, for every pair of integers, an antilinear zeroth-order term on the cylinder whose zeros have the normal form required for Cauchy–Riemann operators with a large antilinear perturbation, and whose asymptotic loops are the model loops $e^{2\pi i a t}$, $e^{2\pi i b t}$; it is used to build reference operators with prescribed asymptotic Conley–Zehnder indices.
--
--   **Formalization Note** Points of the cylinder are pairs `(s, t) : ℝ × ℝ` with `β (s, t + 1) = β (s, t)`; the derivative bound is `‖fderiv ℝ β x‖ ≤ C` for all `x`; smoothness is `ContDiff ℝ ∞ β`; the normal forms are stated as `β (ζ.1 + z.re, ζ.2 + z.im) = z` (resp. `starRingEnd ℂ z`) for `‖z‖ < r`; the end loops are written `Complex.exp (2 * Real.pi * a * t * Complex.I)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For all integers `a` and `b` there is a smooth function `β : ℝ × S¹ → ℂ` with bounded
derivative such that `β(s, t) → e^{2πiat}` as `s → +∞` and `β(s, t) → e^{2πibt}` as `s → -∞`,
uniformly in `t`, with `c ≤ |β| ≤ 1/c` for large `|s|`, whose zeros (mod `t ↦ t + 1`) are the finite
sets `Z⁺ ∪ Z⁻` inside the band `|s| < 1`, and with the normal forms `β(ζ + z) = z` (`ζ ∈ Z⁺`) and
`β(ζ + z) = z̄` (`ζ ∈ Z⁻`) on discs of radius `r`. If `b ≤ a` then `Z⁻ = ∅` and `#Z⁺ = a - b`;
if `a ≤ b` then `Z⁺ = ∅` and `#Z⁻ = b - a`. -/
theorem exists_antilinear_profile (a b : ℤ) :
    ∃ (β : ℝ × ℝ → ℂ) (Zplus Zminus : Finset (ℝ × ℝ)) (r : ℝ),
      ContDiff ℝ ∞ β ∧ (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C) ∧
      (∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) ∧
      (∀ ε > 0, ∃ R : ℝ, ∀ s t,
        (R ≤ s → ‖β (s, t) - Complex.exp (2 * Real.pi * a * t * Complex.I)‖ ≤ ε) ∧
        (s ≤ -R → ‖β (s, t) - Complex.exp (2 * Real.pi * b * t * Complex.I)‖ ≤ ε)) ∧
      (∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1) ∧ Disjoint Zplus Zminus ∧
      (∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m)) ∧
      0 < r ∧ (∀ ζ ∈ Zplus ∪ Zminus, |ζ.1| + r ≤ 1) ∧
      (∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z) ∧
      (∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z) ∧
      (b ≤ a → Zminus = ∅ ∧ (Zplus.card : ℤ) = a - b) ∧
      (a ≤ b → Zplus = ∅ ∧ (Zminus.card : ℤ) = b - a) := by
  sorry

end CauchyRiemannIndex
