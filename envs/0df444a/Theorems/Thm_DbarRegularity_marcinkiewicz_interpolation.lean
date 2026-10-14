-- Prove2me | Theorems.Thm_DbarRegularity_marcinkiewicz_interpolation
-- name    : DbarRegularity.marcinkiewicz_interpolation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:53:02.112073+00:00
-- url     : https://prove2.me/theorems/f01ae2c5-fa8f-4495-8a20-41f98173374a
-- title:
--   The Marcinkiewicz interpolation theorem for sub-additive operators
-- statement:
--   Let $1<r\le\infty$ and let $T$ be a map from $L^1(\mathbb{R}^d)+L^r(\mathbb{R}^d)$ to measurable functions on $\mathbb{R}^d$. $\mathbb{R}^d$ carries Lebesgue measure $m$, and $\|\cdot\|_p$ is the $L^p(\mathbb{R}^d)$ norm. Assume that for all $f,g\in L^1+L^r$:
--
--   1. $|T(f+g)(x)|\le|Tf(x)|+|Tg(x)|$ for almost every $x$;
--   2. $m\{x:|Tf(x)|>\alpha\}\le\dfrac{A_1}{\alpha}\|f\|_1$ for $f\in L^1$ and $\alpha>0$;
--   3. if $r<\infty$: $m\{x:|Tf(x)|>\alpha\}\le\Big(\dfrac{A_r}{\alpha}\|f\|_r\Big)^r$ for $f\in L^r$ and $\alpha>0$; if $r=\infty$: $\|Tf\|_\infty\le A_r\|f\|_\infty$ for $f\in L^\infty$.
--
--   Then for every $1<p<r$ there is a constant $A_p$, depending only on $A_1$, $A_r$, $p$ and $r$, such that $\|Tf\|_p\le A_p\|f\|_p$ for every $f\in L^p(\mathbb{R}^d)$.
--
--   **Formalization Note** $T$ acts on functions `EuclideanSpace ℝ (Fin d) → ℂ`. Membership in $L^1+L^r$ is written out as `∃ f₁ f₂, MemLp f₁ 1 ∧ MemLp f₂ r ∧ f = f₁ + f₂`, and measurability of $Tf$ is assumed for such $f$. Sub-additivity is assumed almost everywhere (Stein writes it pointwise). The exponents $r,p$ are in `ℝ≥0∞`; the case $r=\infty$ uses Stein's form (17) in place of a weak-type bound. $A_1,A_r,A_p\in$ `ℝ≥0`, and $A_p$ is chosen before $d$ and $T$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter I, § 4.2, Theorem 5, p. 21 (with the definitions (17), (18) of § 4.1, p. 20)

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter I, § 4.2, Theorem 5 (p. 21), Marcinkiewicz interpolation:
let `1 < r ≤ ∞` and let `T` map `L¹(ℝ^d) + L^r(ℝ^d)` to measurable functions. Suppose `T` is
sub-additive, of weak type `(1, 1)` with constant `A₁`, and of weak type `(r, r)` with constant
`A_r` (for `r = ∞`: `‖T f‖_∞ ≤ A_r ‖f‖_∞`, Stein's form (17)). Then `‖T f‖_p ≤ A_p ‖f‖_p` for
`f ∈ L^p`, `1 < p < r`, where `A_p` depends only on `A₁`, `A_r`, `p` and `r`. -/
theorem marcinkiewicz_interpolation (r p : ℝ≥0∞) (hr : 1 < r) (hp : 1 < p) (hpr : p < r)
    (A₁ Ar : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ (d : ℕ)
      (T : (EuclideanSpace ℝ (Fin d) → ℂ) → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ f, (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧ f = f₁ + f₂) →
        AEStronglyMeasurable (T f) volume) →
      (∀ f g, (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧ f = f₁ + f₂) →
        (∃ g₁ g₂, MemLp g₁ 1 volume ∧ MemLp g₂ r volume ∧ g = g₁ + g₂) →
        ∀ᵐ x, ‖T (f + g) x‖ ≤ ‖T f x‖ + ‖T g x‖) →
      (∀ f, MemLp f 1 volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖T f x‖ₑ} ≤ (A₁ : ℝ≥0∞) / α * eLpNorm f 1 volume) →
      (r ≠ ⊤ → ∀ f, MemLp f r volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖T f x‖ₑ} ≤ ((Ar : ℝ≥0∞) / α * eLpNorm f r volume) ^ r.toReal) →
      (r = ⊤ → ∀ f, MemLp f ⊤ volume → eLpNorm (T f) ⊤ volume ≤ Ar * eLpNorm f ⊤ volume) →
      ∀ f, MemLp f p volume → eLpNorm (T f) p volume ≤ A * eLpNorm f p volume := by sorry

end DbarRegularity
