-- Prove2me | Theorems.Thm_FDivToolkit_proposition_3
-- name    : FDivToolkit.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:04.476787+00:00
-- url     : https://prove2.me/theorems/bd38de71-7d13-4df8-91e6-6aa1239650bd
-- title:
--   Proposition 3 — a heavier power tail gives infinite divergence
-- statement:
--   Let $\theta>1$ and $t\in(1,\theta)$. Let $H$ be a generating function and $\nu$ a reference model with density $f$, with $\varphi=-\log f$. Assume that
--
--   1. $F(0)<\infty$;
--   2. there exists $\hat x\in(0,\infty)$ with $(\hat x,\infty)\subset\mathcal S$;
--   3. there exists $\tilde y\in(1,\infty)$ such that $H$ is continuously differentiable on $(\tilde y,\infty)$;
--   4. $\limsup_{y\to\infty}H'(y)/H(y)<\infty$;
--   5. for all $c\in(0,\infty)$, $\liminf_{x\to\infty}H(\varphi(x)-(t+1)\log x-c)/x^t>0$.
--
--   Let $\eta$ be a distribution on $\mathcal S$, absolutely continuous with respect to $\nu$, with density $g$, such that $\liminf_{x\to\infty}x^{t+1}g(x)>0$ and $\lim_{x\to\infty}g(x)/f(x)=\infty$. Then
--   $$
--   D_F(\eta\,|\,\nu)=+\infty.
--   $$
--
--   So models with a power tail and an infinite moment of order $t<\theta$ lie outside every divergence ball.
--
--   Differences from the source:
--   - encoding: ϕ = −log f, which is +∞ where f = 0, and lim inf_{x→∞} H(ϕ(x) − (t+1) log x − c)/x^t > 0 → ∃ ε > 0, eventually f x = 0 or ε x^t ≤ H(−log f x − (t+1) log x − c); reason: where f = 0 the paper's quotient is +∞, so that alternative is the paper's case; the condition is equivalent to the paper's
--   - encoding: lim sup_{y→∞} H′(y)/H(y) < ∞ → ∃ C, eventually H′(y) ≤ C H(y); reason: H > 0 on (0, ∞), so the two conditions are equivalent
--   - encoding: lim_{x→∞} g(x)/f(x) = ∞ and lim inf_{x→∞} x^{t+1}g(x) > 0 → ∀ M, eventually M f x < g x; and ∃ δ > 0, eventually δ ≤ x^{t+1} g x; reason: no quotient, since Lean's x/0 = 0 is not the paper's value
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Proposition 3, p.11

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_fDiv
import Definitions.Def_FDivToolkit_Fh

open MeasureTheory Filter Set
open scoped ENNReal

namespace FDivToolkit

/-- Proposition 3, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.11. Let `θ > 1` and
`t ∈ (1, θ)`. Assume `F(0) < ∞`, that `(x̂, ∞) ⊂ 𝓢` for some `x̂ ∈ (0, ∞)`, that `H` is continuously
differentiable on `(ỹ, ∞)` for some `ỹ ∈ (1, ∞)`, that `lim sup_{y→∞} H′(y)/H(y) < ∞`, and that
`lim inf_{x→∞} H(ϕ(x) − (t+1) log x − c)/x^t > 0` for all `c ∈ (0, ∞)`. Let η be a distribution on `𝓢`,
absolutely continuous with respect to ν, with density `g`. Suppose `lim inf_{x→∞} x^{t+1} g(x) > 0`
and `lim_{x→∞} g(x)/f(x) = ∞`. Then `D_F(η|ν) = +∞`.

**Formalization Note.** The paper's `ϕ = −log f` is `+∞` where `f = 0`, where the quotient in the
lim inf condition is `+∞`; hence the alternative `f x = 0`. The condition `g/f → ∞` is written
without a quotient, as `M * f x < g x` eventually for every `M`. -/
theorem proposition_3 {H f g : ℝ → ℝ} {θ t : ℝ} (hH : IsAdmissibleH H) (hf : IsRefModel f)
    (hθ : 1 < θ) (ht : t ∈ Ioo 1 θ) (hF0 : F0 H < ⊤)
    (hS : ∃ xhat : ℝ, 0 < xhat ∧ Ioi xhat ⊆ refSupport f)
    (hC1 : ∃ ytilde : ℝ, 1 < ytilde ∧ ContDiffOn ℝ 1 H (Ioi ytilde))
    (hC : ∃ C : ℝ, ∀ᶠ y in atTop, deriv H y ≤ C * H y)
    (hϕ : ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ x in atTop,
      f x = 0 ∨ ε * x ^ t ≤ H (-Real.log (f x) - (t + 1) * Real.log x - c))
    (hg : IsDensity g) (hac : densityMeasure g ≪ densityMeasure f)
    (hgtail : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in atTop, δ ≤ x ^ (t + 1) * g x)
    (hratio : ∀ M : ℝ, ∀ᶠ x in atTop, M * f x < g x) :
    fDiv (Fbar H) f g = ⊤ := by sorry

end FDivToolkit
